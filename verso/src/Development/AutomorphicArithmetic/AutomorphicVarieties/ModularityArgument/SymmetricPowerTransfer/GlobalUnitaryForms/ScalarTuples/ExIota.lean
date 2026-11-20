import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSClsD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSTest
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSUnit

open NumberField IsDedekindDomain Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

/- English proof (translation)
Establish `h` using `(FiniteAdeleRing.algebraMap (𝓞 F) F t).2`. Use `filter_upwards [h] with v hv`. Conclude with `isIntegral_Ov.2 hv`.
-/
private theorem eventually_isIntegral_cv {F : Type} [Field F] [NumberField F] (t : F) :
    ∀ᶠ v : Pl F in Filter.cofinite, IsIntegral (Ov v) (cv v t) := by
  have h := (FiniteAdeleRing.algebraMap (𝓞 F) F t).2
  filter_upwards [h] with v hv
  exact isIntegral_Ov.2 hv

/- English proof (translation)
Use `filter_upwards [eventually_isIntegral_cv Δ, eventually_isIntegral_cv a.re, eventually_isIntegral_cv a.im] with v h1 h2 h3`. Establish `key` using `isIntegral_of_coords (O := Ov v) (a := lmap (cv v) Δ a) (m := 1) isIntegral_one (by simpa using h1) h2 h3`. Simplify using `using key`.
-/
private theorem ae_int {F : Type} [Field F] [NumberField F] {Δ : F} (a : Lsq F Δ) :
    ∀ᶠ v : Pl F in Filter.cofinite, IsIntegral (Ov v) (lmap (cv v) Δ a) := by
  filter_upwards [eventually_isIntegral_cv Δ, eventually_isIntegral_cv a.re, eventually_isIntegral_cv a.im] with v h1 h2 h3
  have key := isIntegral_of_coords (O := Ov v) (a := lmap (cv v) Δ a) (m := 1) isIntegral_one
    (by simpa using h1) h2 h3
  simpa using key

private def dmap {K K' : Type} [Field K] [Field K'] (f : K →+* K') (Δ : K) : DX Δ →* DX (f Δ) :=
  ((GeneralLinearGroup.map (lmap f Δ)).comp (DX Δ).subtype).codRestrict _ fun γ => mem_DX.2 (by
    have e : ∀ y : Lsq K Δ, lmap f Δ (star y) = star (lmap f Δ y) := fun y => by ext <;> simp [lmap]
    refine ⟨?_, ?_⟩
    · change lmap f Δ (mt γ 1 1) = star (lmap f Δ (mt γ 0 0))
      rw [(mt_mem γ).1, e]
    · change lmap f Δ (mt γ 1 0) = -star (lmap f Δ (mt γ 0 1))
      rw [(mt_mem γ).2, map_neg, e])

/- English proof (translation)
Establish `hall : ∀ g : DX Δ, ∀ᶠ v : Pl F in Filter.cofinite, ∀ i j : Fin 2, IsIntegral (Ov v) (Glob.mt (dmap (cv v) Δ g) i j)`. Introduce `g`. Rewrite using `[Filter.eventually_all]`. Introduce `i`. Rewrite using `[Filter.eventually_all]`.

Introduce `j`. Conclude with `ae_int (Glob.mt g i j)`. Use `⟨{ toFun := fun γ => ⟨fun v => dmap (cv v) Δ γ, ?_⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩` and prove the remaining obligations. Use `show ∀ᶠ v in Filter.cofinite, dmap (cv v) Δ γ ∈ KD (cv v Δ) (Ov v) filter_upwards [hall γ, hall γ⁻¹] with v h1 h2`. Rewrite using `[mem_KD]`.

Use `⟨h1, fun i j => ?_⟩` and prove the remaining obligations. Establish `h` using `h2 i j`. Rewrite `h` using `[map_inv]`. Then use the resulting hypothesis. Conclude with `Subtype.ext (funext fun v => map_one _)`. Conclude with `fun a b => Subtype.ext (funext fun v => map_mul _ a b)`.

Introduce `γ v`. Both sides reduce to the same expression.
-/
private theorem ex_iota {F : Type} [Field F] [NumberField F] (Δ : F) : ∃ ι : DX Δ →* DA Δ, IsIotaD ι := by
  have hall : ∀ g : DX Δ, ∀ᶠ v : Pl F in Filter.cofinite,
      ∀ i j : Fin 2, IsIntegral (Ov v) (Glob.mt (dmap (cv v) Δ g) i j) := by
    intro g
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact ae_int (Glob.mt g i j)
  refine ⟨{ toFun := fun γ => ⟨fun v => dmap (cv v) Δ γ, ?_⟩,
            map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · show ∀ᶠ v in Filter.cofinite, dmap (cv v) Δ γ ∈ KD (cv v Δ) (Ov v)
    filter_upwards [hall γ, hall γ⁻¹] with v h1 h2
    rw [mem_KD]
    refine ⟨h1, fun i j => ?_⟩
    have h := h2 i j
    rwa [map_inv] at h
  · exact Subtype.ext (funext fun v => map_one _)
  · exact fun a b => Subtype.ext (funext fun v => map_mul _ a b)
  · intro γ v
    rfl

/- English proof (translation)
Introduce `F _ _ Δ D h V _ _ ch x B hB`. Use `h.real` as an intermediate fact. Take `⟨ι, hι⟩` from `ex_iota Δ`. Conclude with `⟨⟨finS_cls_of D ι hι (clsD h.neg ι hι) (relIndex_normOneLevel_maximalCompact_ne_zero D h) hB, finS_stab D h (normOneLevel_le_maximalCompact D h) hB⟩, finS_test F Δ D h V ch x B hB⟩`.
-/
theorem UpperTheory.V.Z.Sym.Glob.finS :
    UpperTheory.V.Z.Sym.Glob.FinS := by
  intro F _ _ Δ D h V _ _ ch x B hB
  have := h.real
  obtain ⟨ι, hι⟩ := ex_iota Δ
  exact ⟨⟨finS_cls_of D ι hι (clsD h.neg ι hι) (relIndex_normOneLevel_maximalCompact_ne_zero D h) hB, finS_stab D h (normOneLevel_le_maximalCompact D h) hB⟩,
    finS_test F Δ D h V ch x B hB⟩
