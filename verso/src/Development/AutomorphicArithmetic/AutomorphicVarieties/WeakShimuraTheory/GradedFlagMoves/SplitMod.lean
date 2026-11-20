import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.DecCyc

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD w hw A hwA hlA hdec`. Establish `hlw : l ≠ w`. Introduce and unpack `rfl`. Conclude with `hlA hwA`. Take `⟨-, -, γ, hγ, -, hcyc⟩` from `UpperTheory.V.Chr.decCyc Ω w A hw hwA`.

Establish `hγl : ((cycZ ℚ Ω l γ : ℤ_[l]ˣ) : ℤ_[l]) = w` using `hcyc l hlw`. Establish `hom : D.om γ = 1` using `hdec hγ`. Establish `hbar` using `hD.om_bar γ`. Simplify using `only [Raw.bar, hom, chiO, MonoidHom.comp_apply, Units.coe_map, Units.val_one, map_one, MonoidHom.coe_coe, hγl] at hbar`. Establish `hbar' : residue c.O (algebraMap ℤ_[l] c.O (w : ℤ_[l])) = 1` using `hbar.symm`.

Establish `hint : Algebra.IsIntegral ℤ_[l] c.O` using `by haveI := c.fin infer_instance`. Establish `key : ((w : ℤ_[l]) - 1) ∈ IsLocalRing.maximalIdeal ℤ_[l]`. Establish `h0 : residue c.O (algebraMap ℤ_[l] c.O ((w : ℤ_[l]) - 1)) = 0`. Rewrite using `[map_sub, map_one, map_sub, map_one, hbar', sub_self]`. Establish `hm` using `(IsLocalRing.residue_eq_zero_iff _).mp h0`.

Establish `hmax : (IsLocalRing.maximalIdeal c.O).comap (algebraMap ℤ_[l] c.O) = IsLocalRing.maximalIdeal ℤ_[l]` using `IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)`. Rewrite using `[← hmax]`. Conclude with `hm`. Establish `hcast : ((w : ℤ_[l]) - 1) = (((w : ℤ) - 1 : ℤ) : ℤ_[l])` using `by push_cast; rfl`. Rewrite `key` using `[hcast, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_int_lt_one_iff_dvd]`.

Establish `h1 : ((w - 1 : ℕ) : ℤ) = (w : ℤ) - 1`. Rewrite using `[Nat.cast_sub hw.one_le, Nat.cast_one]`. Rewrite `key` using `[← h1]`. Conclude with `Int.natCast_dvd_natCast.mp key`.
-/
theorem UpperTheory.V.Ws.Rt.splitMod :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ w : ℕ, w.Prime →
      ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → ¬ A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ D.om.ker → l ∣ w - 1 := by
  intro Ω _ _ _ l _ c D hD w hw A hwA hlA hdec
  have hlw : l ≠ w := by
    rintro rfl; exact hlA hwA
  obtain ⟨-, -, γ, hγ, -, hcyc⟩ := UpperTheory.V.Chr.decCyc Ω w A hw hwA
  have hγl : ((cycZ ℚ Ω l γ : ℤ_[l]ˣ) : ℤ_[l]) = w := hcyc l hlw
  have hom : D.om γ = 1 := hdec hγ
  have hbar := hD.om_bar γ
  simp only [Raw.bar, hom, chiO, MonoidHom.comp_apply, Units.coe_map, Units.val_one, map_one,
    MonoidHom.coe_coe, hγl] at hbar
  have hbar' : residue c.O (algebraMap ℤ_[l] c.O (w : ℤ_[l])) = 1 := hbar.symm
  have hint : Algebra.IsIntegral ℤ_[l] c.O := by
    haveI := c.fin
    infer_instance
  have key : ((w : ℤ_[l]) - 1) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    have h0 : residue c.O (algebraMap ℤ_[l] c.O ((w : ℤ_[l]) - 1)) = 0 := by
      rw [map_sub, map_one, map_sub, map_one, hbar', sub_self]
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp h0
    have hmax : (IsLocalRing.maximalIdeal c.O).comap (algebraMap ℤ_[l] c.O) = IsLocalRing.maximalIdeal ℤ_[l] :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
    rw [← hmax]
    exact hm
  have hcast : ((w : ℤ_[l]) - 1) = (((w : ℤ) - 1 : ℤ) : ℤ_[l]) := by push_cast; rfl
  rw [hcast, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_int_lt_one_iff_dvd] at key
  have h1 : ((w - 1 : ℕ) : ℤ) = (w : ℤ) - 1 := by
    rw [Nat.cast_sub hw.one_le, Nat.cast_one]
  rw [← h1] at key
  exact Int.natCast_dvd_natCast.mp key
