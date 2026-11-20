import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsEtaCharacterImaginaryQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EulerProductInductionSupported
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFiniteOrderHeckeCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.GlobTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `x hx` and use `by rw [MonoidHom.mul_apply, ha x hx, hb x hx, one_mul]`.
-/
private theorem unr_mul {a b : kˣ →* ℂˣ} (ha : IsUnram a) (hb : IsUnram b) : IsUnram (a * b) := fun x hx => by
  rw [MonoidHom.mul_apply, ha x hx, hb x hx, one_mul]

/- English proof (translation)
Introduce `x hx` and use `by rw [MonoidHom.inv_apply, ha x hx, inv_one]`.
-/
private theorem unr_inv {a : kˣ →* ℂˣ} (ha : IsUnram a) : IsUnram a⁻¹ := fun x hx => by
  rw [MonoidHom.inv_apply, ha x hx, inv_one]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => by simpa using unr_mul h (unr_inv hμ), fun h => unr_mul h hμ⟩`.
-/
private theorem unr_mul_iff {a μ : kˣ →* ℂˣ} (hμ : IsUnram μ) : IsUnram (a * μ) ↔ IsUnram a :=
  ⟨fun h => by simpa using unr_mul h (unr_inv hμ), fun h => unr_mul h hμ⟩

/- English proof (translation)
Unfold `lin`. Distinguish the cases in `h : IsUnram ξ`. Rewrite using `[if_pos ((unr_mul_iff hμ).2 h), if_pos h]`. Simplify using `[MonoidHom.mul_apply, mul_assoc]`. Rewrite using `[if_neg (fun h' => h ((unr_mul_iff hμ).1 h')), if_neg h]`.

Simplify using the standard rewrite rules.
-/
private theorem lin_shift (ξ μ : kˣ →* ℂˣ) (hμ : IsUnram μ) :
    lin (ξ * μ) = (lin ξ).comp (C ((μ (unif k) : ℂˣ) : ℂ) * X) := by
  unfold lin
  by_cases h : IsUnram ξ
  · rw [if_pos ((unr_mul_iff hμ).2 h), if_pos h]
    simp [MonoidHom.mul_apply, mul_assoc]
  · rw [if_neg (fun h' => h ((unr_mul_iff hμ).1 h')), if_neg h]
    simp

/- English proof (translation)
Unfold `lin3`. Rewrite using `[← mul_assoc ν, ← mul_assoc ν⁻¹, lin_shift _ _ hμ, lin_shift _ _ hμ, lin_shift _ _ hμ]`. Simplify using `[mul_comp]`.
-/
private theorem linear_factor_unramified_twist (ν c μ : kˣ →* ℂˣ) (hμ : IsUnram μ) :
    lin3 ν (c * μ) = (lin3 ν c).comp (C ((μ (unif k) : ℂˣ) : ℂ) * X) := by
  unfold lin3
  rw [← mul_assoc ν, ← mul_assoc ν⁻¹, lin_shift _ _ hμ, lin_shift _ _ hμ, lin_shift _ _ hμ]
  simp [mul_comp]

end Loc

/- English proof (translation)
Take `⟨hu, he⟩` from `(h2 ℚ K v w μ).1 hμ`. Establish `e1 : (θ * μ).comp (nm w) = θ.comp (nm w) * μ.comp (nm w)` using `rfl`. Establish `e2` using `((h1 (w.1.adicCompletion K)).2.2.2 s (θ.comp (nm w))).2.2.2 (μ.comp (nm w)) hu`. Rewrite using `[e1, e2, comp_assoc, comp_assoc]`. Use `congr 1`.

Simplify using `only [MonoidHom.comp_apply, he, Units.val_pow_eq_pow_val, X_pow_comp, mul_comp, C_comp, X_comp, mul_pow, C_pow, Polynomial.pow_comp]`.
-/
private theorem pol_shift (h1 : PolFacts) (h2 : NormVal) (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 ℚ))
    (w : PlacesOver K v) (s : Multiset (IrrGL (w.1.adicCompletion K))) (θ μ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hμ : IsUnram μ) :
    (pol s ((θ * μ).comp (nm w))).comp (X ^ fdeg w) =
      ((pol s (θ.comp (nm w))).comp (X ^ fdeg w)).comp (C ((μ (unif (v.adicCompletion ℚ)) : ℂˣ) : ℂ) * X) := by
  obtain ⟨hu, he⟩ := (h2 ℚ K v w μ).1 hμ
  have e1 : (θ * μ).comp (nm w) = θ.comp (nm w) * μ.comp (nm w) := rfl
  have e2 := ((h1 (w.1.adicCompletion K)).2.2.2 s (θ.comp (nm w))).2.2.2 (μ.comp (nm w)) hu
  rw [e1, e2, comp_assoc, comp_assoc]
  congr 1
  simp only [MonoidHom.comp_apply, he, Units.val_pow_eq_pow_val, X_pow_comp, mul_comp, C_comp, X_comp, mul_pow, C_pow,
    Polynomial.pow_comp]

/- English proof (translation)
The claim follows from `(normVal ℚ K v w μ).1 hμ |>.1`.
-/
private theorem unr_comp (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 ℚ)) (w : PlacesOver K v)
    (μ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hμ : IsUnram μ) : IsUnram (μ.comp (nm w)) := (normVal ℚ K v w μ).1 hμ |>.1

/- English proof (translation)
The claim follows from `MonoidHom.ext fun x => Units.ext (by rw [MonoidHom.mul_apply, Units.val_mul, Ad3P.DihedralUnramifiedPlaces.loc_eq, GroundTheory.Automorphic.GodementSection.coe_localChar, GroundTheory.Automorphic.GodementSection.coe_localChar, GroundTheory.Automorphic.GodementSection.coe_localCha …`.
-/
private theorem loc_mul (c η : HeckeCharacter ℚ) (u : Ad3.Pl) : localChar (c * η) u = localChar c u * (toH η).loc u :=
  MonoidHom.ext fun x => Units.ext (by
    rw [MonoidHom.mul_apply, Units.val_mul, Ad3P.DihedralUnramifiedPlaces.loc_eq, GroundTheory.Automorphic.GodementSection.coe_localChar,
      GroundTheory.Automorphic.GodementSection.coe_localChar, GroundTheory.Automorphic.GodementSection.coe_localChar,
      HeckeCharacter.localComponent_apply, HeckeCharacter.localComponent_apply, HeckeCharacter.localComponent_apply]
    rfl)

/- English proof (translation)
Establish `hF` using `suppFacts K 3 (by norm_num) P`. Use `choose s hs using fun w => (hF w).1`. Establish `hR : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, w ∉ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K` using `(Finset.finite_toSet _).compl_mem_cofinite`. Establish `hE : ∀ᶠ u : Ad3.Pl in Filter.cofinite, u ≠ v ∧ u ∉ D.bad ∧ (toH η).UnrAt u ∧ ∀ w : PlacesOver K u, IsPrimitiveRoot ((toH η).val u) (fdeg w) ∧ Fintype.card (PlacesOver K u) * fdeg w = 2 ∧ w.1 ∉ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ∧ (CG.mk P).HasSat w.1 {D.ν u (un …`. Establish `h1 : ∀ᶠ u : Ad3.Pl in Filter.cofinite, u ≠ v` using `(Set.finite_singleton v).compl_mem_cofinite`.

Establish `h3 : ∀ᶠ u : Ad3.Pl in Filter.cofinite, u ∉ D.bad` using `(Finset.finite_toSet _).compl_mem_cofinite`. Use `filter_upwards [hη.ae, hSys, IdeleNorm.eventually_forall_placesOver ℚ hR, h1, h3] with u a b c d e`. Conclude with `⟨d, e, a.1, fun w => ⟨(a.2 w).1, (a.2 w).2, c w, b w⟩⟩`. Use `set S₀ : Finset Ad3.Pl := (Filter.eventually_cofinite.1 hE).toFinset with hS₀`. Establish `hgood : ∀ u ∉ S₀, _` using `fun u hu => by`.

Simplify `hu` using `only [hS₀, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not]`. Establish `hv : v ∈ S₀`. Assume the negation of the conclusion as `h`. Conclude with `(hgood v h).1 rfl`. Establish `hbad : D.bad ⊆ S₀` using `fun u hu => by`.

Assume the negation of the conclusion as `h`. Conclude with `(hgood u h).2.1 hu`. Set `bad : ∀ u : Ad3.Pl, Finset ((u.adicCompletion ℚ)ˣ →* ℂˣ)` to `fun u => {D.ν u, 1, (D.ν u)⁻¹, D.ν u * (toH η).loc u, (toH η).loc u, (D.ν u)⁻¹ * (toH η).loc u}`. Set `bad' : ∀ w : HeightOneSpectrum (𝓞 K), Finset ((w.adicCompletion K)ˣ →* ℂˣ)` to `fun w => (s w).toFinset.image fun y => if h : ∃ ξ hξ, y = IrrGL.ofChar ξ hξ then h.choose else 1`. Establish `hbad' : ∀ w, ∀ ζ ∈ chars (s w), ζ ∈ bad' w`.

Introduce and unpack `w ζ ⟨hζ, hm⟩`. Use `Finset.mem_image.2 ⟨_, Multiset.mem_toFinset.2 hm, ?_⟩` and prove the remaining obligations. Establish `h : ∃ ξ hξ, IrrGL.ofChar ζ hζ = IrrGL.ofChar ξ hξ` using `⟨ζ, hζ, rfl⟩`. Rewrite using `[dif_pos h]`. Take `⟨hξ, e⟩` from `h.choose_spec`.

Conclude with `((polFacts _).2.2.1 _ _ _ _ e).symm`. Take `⟨χ, hχv, hχ⟩` from `globTw ℚ K v θ hθ S₀ bad bad'`. Take `⟨c, hc, hcu⟩` from `UpperTheory.exists_finite_order_hecke_character χ`. Establish `key : ∀ (u : Ad3.Pl) (ξ : (u.adicCompletion ℚ)ˣ →* ℂˣ), ¬ IsUnram (ξ * χ.loc u) → ¬ IsUnram (ξ * localChar c u)` using `fun u ξ h h' => h (by`. Use `unr_mul h' (hcu u)` as an intermediate fact.

Rewrite using `[mul_comm (χ.loc u), ← mul_assoc, mul_assoc ξ, mul_inv_cancel, mul_one] at this)` and apply the resulting hypothesis. Establish `hdeep : ∀ u ∈ S₀, u ≠ v → Ram3 (D.ν u) (localChar c u) ∧ Ram3 (D.ν u) (localChar (c * η) u) ∧ ∀ w : PlacesOver K u, ∀ ζ ∈ chars (s w.1), ¬ IsUnram (ζ * (localChar c u).comp (nm w))`. Introduce `u hu hne`. Take `⟨h1, h3⟩` from `hχ u hu hne`. Establish `hb` using `fun ξ (hξ : ξ ∈ bad u) => key u ξ (h1 ξ hξ)`.

Rewrite using `[loc_mul]`. Use `⟨⟨hb _ (by simp [bad]), by simpa using hb 1 (by simp [bad]), hb _ (by simp [bad])⟩, ⟨?_, ?_, ?_⟩, fun w ζ hζ h' => h3 w ζ (hbad' _ _ hζ) ?_⟩` and prove the remaining obligations. Use `hb (D.ν u * (toH η).loc u) (by simp [bad])` as an intermediate fact. Rewrite `this` using `[mul_assoc, mul_comm ((toH η).loc u)]`. Then use the resulting hypothesis. Use `hb ((toH η).loc u) (by simp [bad])` as an intermediate fact.

Rewrite `this` using `[mul_comm]`. Then use the resulting hypothesis. Use `hb ((D.ν u)⁻¹ * (toH η).loc u) (by simp [bad])` as an intermediate fact. Rewrite `this` using `[mul_assoc, mul_comm ((toH η).loc u)]`. Then use the resulting hypothesis. Use `unr_mul h' (unr_comp K u w _ (hcu u))` as an intermediate fact. Establish `e : (χ.loc u).comp (nm w) = (localChar c u).comp (nm w) * (χ.loc u * (localChar c u)⁻¹).comp (nm w)`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite `this` using `[mul_assoc, ← e]`. Then use the resulting hypothesis. Establish `core` using `UpperTheory.euler_product_induction_supported K h2 D hAn P η c hη hc S₀ v s hs hbad hv (fun u hu => (hgood u hu).2.2) hdeep`. Use `set θc := localChar c v with hθc`.

Establish `hμ : IsUnram (θ * θc⁻¹)`. Use `unr_mul (unr_inv hχv) (hcu v)` as an intermediate fact. Establish `e : (χ.loc v * θ⁻¹)⁻¹ * (χ.loc v * (localChar c v)⁻¹) = θ * θc⁻¹`. Rewrite using `[mul_inv, inv_inv, mul_comm (χ.loc v)⁻¹, mul_assoc, inv_mul_cancel_left]`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.

Use `set μ := θ * θc⁻¹ with hμd`. Establish `eθ : θ = θc * μ` using `by rw [hμd, mul_comm θ, mul_inv_cancel_left]`. Establish `e0 : s' = fun w : PlacesOver K v => s w.1` using `funext fun w => (hF w.1).2.1 _ _ (hs' w) (hs w.1)`. Substitute `e0` using the available equality. Establish `l0 : ((toH η) ^ 0).loc v = 1` using `by rw [pow_zero]; rfl`.

Establish `e2 : θ * (toH η).loc v = localChar (c * η) v * μ`. Rewrite using `[loc_mul, ← hθc]`. Conclude with `(congrArg (· * (toH η).loc v) eθ).trans (mul_right_comm _ _ _)`. Establish `e3 : ∏ j ∈ Finset.range 2, lin (D.ν v * (θ * ((toH η) ^ j).loc v)) * lin (θ * ((toH η) ^ j).loc v) * lin ((D.ν v)⁻¹ * (θ * ((toH η) ^ j).loc v)) = lin3 (D.ν v) θ * lin3 (D.ν v) (θ * (toH η).loc v)`. Simplify using `only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, l0, mul_one, pow_one, lin3]`.

Rewrite using `[e3, e2, linear_factor_unramified_twist _ _ _ hμ]`. Use `conv_lhs => rw [eθ, linear_factor_unramified_twist _ _ _ hμ]`. Rewrite using `[← mul_comp, core, Polynomial.prod_comp]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [eθ]`.

Rewrite using `[pol_shift polFacts normVal K v w _ _ _ hμ]`.
-/
private theorem step (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (D : Ad3.Dat)
    (hAn : Ad3.An D) (P : CuspSub K 3) (hSys : AdSys D P) (η : HeckeCharacter ℚ) (hη : EtaOK K η) (v : HeightOneSpectrum (𝓞 ℚ))
    (s' : ∀ w : PlacesOver K v, Multiset (IrrGL (w.1.adicCompletion K))) (hs' : ∀ w, SuppAt P w.1 (s' w))
    (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hθ : IsSmoothChar θ) :
    ∏ j ∈ Finset.range 2, lin (D.ν v * (θ * ((toH η) ^ j).loc v)) * lin (θ * ((toH η) ^ j).loc v) *
        lin ((D.ν v)⁻¹ * (θ * ((toH η) ^ j).loc v)) =
      ∏ w, (pol (s' w) (θ.comp (nm w))).comp (X ^ fdeg w) := by
  have hF := suppFacts K 3 (by norm_num) P
  choose s hs using fun w => (hF w).1
  have hR : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, w ∉ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K :=
    (Finset.finite_toSet _).compl_mem_cofinite
  have hE : ∀ᶠ u : Ad3.Pl in Filter.cofinite, u ≠ v ∧ u ∉ D.bad ∧ (toH η).UnrAt u ∧ ∀ w : PlacesOver K u,
      IsPrimitiveRoot ((toH η).val u) (fdeg w) ∧ Fintype.card (PlacesOver K u) * fdeg w = 2 ∧
        w.1 ∉ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ∧
        (CG.mk P).HasSat w.1 {D.ν u (unif (u.adicCompletion ℚ)) ^ fdeg w, 1, (D.ν u (unif (u.adicCompletion ℚ)) ^ fdeg w)⁻¹} := by
    have h1 : ∀ᶠ u : Ad3.Pl in Filter.cofinite, u ≠ v := (Set.finite_singleton v).compl_mem_cofinite
    have h3 : ∀ᶠ u : Ad3.Pl in Filter.cofinite, u ∉ D.bad := (Finset.finite_toSet _).compl_mem_cofinite
    filter_upwards [hη.ae, hSys, IdeleNorm.eventually_forall_placesOver ℚ hR, h1, h3] with u a b c d e
    exact ⟨d, e, a.1, fun w => ⟨(a.2 w).1, (a.2 w).2, c w, b w⟩⟩
  set S₀ : Finset Ad3.Pl := (Filter.eventually_cofinite.1 hE).toFinset with hS₀
  have hgood : ∀ u ∉ S₀, _ := fun u hu => by
    simpa only [hS₀, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using hu
  have hv : v ∈ S₀ := by
    by_contra h
    exact (hgood v h).1 rfl
  have hbad : D.bad ⊆ S₀ := fun u hu => by
    by_contra h
    exact (hgood u h).2.1 hu
  let bad : ∀ u : Ad3.Pl, Finset ((u.adicCompletion ℚ)ˣ →* ℂˣ) := fun u =>
    {D.ν u, 1, (D.ν u)⁻¹, D.ν u * (toH η).loc u, (toH η).loc u, (D.ν u)⁻¹ * (toH η).loc u}
  let bad' : ∀ w : HeightOneSpectrum (𝓞 K), Finset ((w.adicCompletion K)ˣ →* ℂˣ) := fun w =>
    (s w).toFinset.image fun y => if h : ∃ ξ hξ, y = IrrGL.ofChar ξ hξ then h.choose else 1
  have hbad' : ∀ w, ∀ ζ ∈ chars (s w), ζ ∈ bad' w := by
    rintro w ζ ⟨hζ, hm⟩
    refine Finset.mem_image.2 ⟨_, Multiset.mem_toFinset.2 hm, ?_⟩
    have h : ∃ ξ hξ, IrrGL.ofChar ζ hζ = IrrGL.ofChar ξ hξ := ⟨ζ, hζ, rfl⟩
    rw [dif_pos h]
    obtain ⟨hξ, e⟩ := h.choose_spec
    exact ((polFacts _).2.2.1 _ _ _ _ e).symm
  obtain ⟨χ, hχv, hχ⟩ := globTw ℚ K v θ hθ S₀ bad bad'
  obtain ⟨c, hc, hcu⟩ := UpperTheory.exists_finite_order_hecke_character χ
  have key : ∀ (u : Ad3.Pl) (ξ : (u.adicCompletion ℚ)ˣ →* ℂˣ), ¬ IsUnram (ξ * χ.loc u) → ¬ IsUnram (ξ * localChar c u) :=
    fun u ξ h h' => h (by
      have := unr_mul h' (hcu u)
      rwa [mul_comm (χ.loc u), ← mul_assoc, mul_assoc ξ, mul_inv_cancel, mul_one] at this)
  have hdeep : ∀ u ∈ S₀, u ≠ v → Ram3 (D.ν u) (localChar c u) ∧ Ram3 (D.ν u) (localChar (c * η) u) ∧
      ∀ w : PlacesOver K u, ∀ ζ ∈ chars (s w.1), ¬ IsUnram (ζ * (localChar c u).comp (nm w)) := by
    intro u hu hne
    obtain ⟨h1, h3⟩ := hχ u hu hne
    have hb := fun ξ (hξ : ξ ∈ bad u) => key u ξ (h1 ξ hξ)
    rw [loc_mul]
    refine ⟨⟨hb _ (by simp [bad]), by simpa using hb 1 (by simp [bad]), hb _ (by simp [bad])⟩,
      ⟨?_, ?_, ?_⟩, fun w ζ hζ h' => h3 w ζ (hbad' _ _ hζ) ?_⟩
    · have := hb (D.ν u * (toH η).loc u) (by simp [bad])
      rwa [mul_assoc, mul_comm ((toH η).loc u)] at this
    · have := hb ((toH η).loc u) (by simp [bad])
      rwa [mul_comm] at this
    · have := hb ((D.ν u)⁻¹ * (toH η).loc u) (by simp [bad])
      rwa [mul_assoc, mul_comm ((toH η).loc u)] at this
    · have := unr_mul h' (unr_comp K u w _ (hcu u))
      have e : (χ.loc u).comp (nm w) = (localChar c u).comp (nm w) * (χ.loc u * (localChar c u)⁻¹).comp (nm w) := by
        ext x
        simp
      rwa [mul_assoc, ← e] at this
  have core := UpperTheory.euler_product_induction_supported K h2 D hAn P η c hη hc S₀ v s hs hbad hv (fun u hu => (hgood u hu).2.2) hdeep
  set θc := localChar c v with hθc
  have hμ : IsUnram (θ * θc⁻¹) := by
    have := unr_mul (unr_inv hχv) (hcu v)
    have e : (χ.loc v * θ⁻¹)⁻¹ * (χ.loc v * (localChar c v)⁻¹) = θ * θc⁻¹ := by
      rw [mul_inv, inv_inv, mul_comm (χ.loc v)⁻¹, mul_assoc, inv_mul_cancel_left]
    rwa [e] at this
  set μ := θ * θc⁻¹ with hμd
  have eθ : θ = θc * μ := by rw [hμd, mul_comm θ, mul_inv_cancel_left]
  have e0 : s' = fun w : PlacesOver K v => s w.1 := funext fun w => (hF w.1).2.1 _ _ (hs' w) (hs w.1)
  subst e0
  have l0 : ((toH η) ^ 0).loc v = 1 := by rw [pow_zero]; rfl
  have e2 : θ * (toH η).loc v = localChar (c * η) v * μ := by
    rw [loc_mul, ← hθc]
    exact (congrArg (· * (toH η).loc v) eθ).trans (mul_right_comm _ _ _)
  have e3 : ∏ j ∈ Finset.range 2, lin (D.ν v * (θ * ((toH η) ^ j).loc v)) * lin (θ * ((toH η) ^ j).loc v) *
        lin ((D.ν v)⁻¹ * (θ * ((toH η) ^ j).loc v)) = lin3 (D.ν v) θ * lin3 (D.ν v) (θ * (toH η).loc v) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, l0, mul_one, pow_one, lin3]
  rw [e3, e2, linear_factor_unramified_twist _ _ _ hμ]
  conv_lhs => rw [eθ, linear_factor_unramified_twist _ _ _ hμ]
  rw [← mul_comp, core, Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun w _ => ?_
  conv_rhs => rw [eθ]
  rw [pol_shift polFacts normVal K v w _ _ _ hμ]

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad

open UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad in
/- English proof (translation)
Introduce `K _ _ _ h2 D hAn P hSys`. Take `⟨η, hη⟩` from `UpperTheory.exists_eta_character_imaginary_quadratic K h2`. Conclude with `⟨toH η, fun v => ⟨fun w => (hη.loc v w).1, fun θ hθ w hw => ((hη.loc v w).2.2 θ hθ).2.2 (by`. Rewrite `*` using `[h2]`. Conclude with `hw), fun s' hs' θ hθ => step K h2 D hAn P hSys η hη v s' hs' θ hθ⟩⟩`.
-/
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.matchAd :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.MatchAd := by
  intro K _ _ _ h2 D hAn P hSys
  obtain ⟨η, hη⟩ := UpperTheory.exists_eta_character_imaginary_quadratic K h2
  exact ⟨toH η, fun v => ⟨fun w => (hη.loc v w).1, fun θ hθ w hw => ((hη.loc v w).2.2 θ hθ).2.2 (by
    rw [h2] at *; exact hw), fun s' hs' θ hθ => step K h2 D hAn P hSys η hη v s' hs' θ hθ⟩⟩
