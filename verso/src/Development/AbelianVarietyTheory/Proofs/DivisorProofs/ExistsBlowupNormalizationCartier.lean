import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
namespace GlobalTheory.FlatModel.BlowupModel

/- English proof (translation)
Rewrite using `[Scheme.preimage_basicOpen, map_natCast]`. Both sides reduce to the same expression.
-/
theorem preimage_basicOpen_natCast (p : ℕ) {X X' : Scheme.{0}} (π : X' ⟶ X) :
    π ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤)) = X'.basicOpen (p : Γ(X', ⊤)) := by
  rw [Scheme.preimage_basicOpen, map_natCast]
  rfl

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `h1 : (q : V) ∈ IsLocalRing.maximalIdeal V` using `h`. Establish `h2 : (p : V) ∈ IsLocalRing.maximalIdeal V` using `ValuationSubring.coe_mem_nonunits_iff.mp (by simpa using hV)`. Establish `hc : IsCoprime (q : ℤ) (p : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hqp)`. Take `⟨a, b, hab⟩` from `hc.map (Int.castRingHom V)`.

Apply `(IsLocalRing.maximalIdeal V).ne_top_iff_one.1 (IsLocalRing.maximalIdeal.isMaximal V).ne_top` to reduce the goal to its premises. Rewrite using `[← hab]`. Simplify using `only [eq_intCast, Int.cast_natCast]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)`.
-/
theorem isUnit_natCast_of_ne {F : Type} [Field F] (V : ValuationSubring F) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hqp : q ≠ p) (hV : (p : F) ∈ V.nonunits) : IsUnit (q : V) := by
  by_contra h
  have h1 : (q : V) ∈ IsLocalRing.maximalIdeal V := h
  have h2 : (p : V) ∈ IsLocalRing.maximalIdeal V := ValuationSubring.coe_mem_nonunits_iff.mp (by simpa using hV)
  have hc : IsCoprime (q : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hqp)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom V)
  apply (IsLocalRing.maximalIdeal V).ne_top_iff_one.1 (IsLocalRing.maximalIdeal.isMaximal V).ne_top
  rw [← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

/- English proof (translation)
Set `φ : V →+* X.residueField y` to `(X.evaluation ⊤ y trivial).hom.comp (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)`. Establish `hpy : (p : X.residueField y) ≠ 0`. Use `(X.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y trivial (p : Γ(X, ⊤))).2 hy` as an intermediate fact. Simplify using `using this`. Establish `hq : ∀ q : ℕ, q.Prime → q ≠ p → (q : X.residueField y) ≠ 0`.

Introduce `q hq hqp`. Establish `hu` using `(isUnit_natCast_of_ne V p q hp.out hq hqp hV).map φ`. Rewrite `hu` using `[map_natCast]`. Conclude with `hu.ne_zero`. Use `ringChar.charP (X.residueField y)` as an intermediate fact.

Break down `CharP.char_is_prime_or_zero (X.residueField y) (ringChar (X.residueField y)) with h | h` into its components or cases. It suffices to derive a contradiction. Establish `h0` using `ringChar.Nat.cast_ringChar (R := X.residueField y)`. Distinguish the cases in `e : ringChar (X.residueField y) = p`. Conclude with `hpy (e ▸ h0)`.

Conclude with `hq _ h e h0`. Use `ringChar.of_eq h` as an intermediate fact. Conclude with `CharP.charP_to_charZero _`.
-/
theorem charZero_residueField {F : Type} [Field F] (V : ValuationSubring F) (p : ℕ) [hp : Fact p.Prime]
    (hV : (p : F) ∈ V.nonunits) {X : Scheme.{0}} (s : X ⟶ Sp V) (y : X)
    (hy : y ∈ X.basicOpen (p : Γ(X, ⊤))) : CharZero (X.residueField y) := by
  let φ : V →+* X.residueField y :=
    (X.evaluation ⊤ y trivial).hom.comp (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)
  have hpy : (p : X.residueField y) ≠ 0 := by
    have := (X.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y trivial (p : Γ(X, ⊤))).2 hy
    simpa using this
  have hq : ∀ q : ℕ, q.Prime → q ≠ p → (q : X.residueField y) ≠ 0 := by
    intro q hq hqp
    have hu := (isUnit_natCast_of_ne V p q hp.out hq hqp hV).map φ
    rw [map_natCast] at hu
    exact hu.ne_zero
  have := ringChar.charP (X.residueField y)
  rcases CharP.char_is_prime_or_zero (X.residueField y) (ringChar (X.residueField y)) with h | h
  · exfalso
    have h0 := ringChar.Nat.cast_ringChar (R := X.residueField y)
    by_cases e : ringChar (X.residueField y) = p
    · exact hpy (e ▸ h0)
    · exact hq _ h e h0
  · have := ringChar.of_eq h
    exact CharP.charP_to_charZero _

end GlobalTheory.FlatModel.BlowupModel

open GlobalTheory.FlatModel.BlowupModel in

/- English proof (translation)
Introduce `F _ _ V p _ hp X s hXi hXn hXp hXf J hJ`. Establish `hDVR` using `(GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V (Fact.out : p.Prime).ne_zero hp).1`. Set `U : X.Opens` to `X.basicOpen (p : Γ(X, ⊤))`. Take `⟨X'', b, hb, hbs, hiso⟩` from `GlobalTheory.ProjBlowup.exists_blowup s hXp J`. Establish `hbU : IsIso (b ∣_ U)` using `hiso U fun x hx hJx => hJ x hJx hx`.

Establish `hN : GlobalTheory.IsNormalScheme X` using `.of_pred hXn`. Establish `e₀ : (b ⁻¹ᵁ U).ι ≫ b = b ∣_ U ≫ U.ι` using `(morphismRestrict_ι b U).symm`. Establish `: IsOpenImmersion ((b ⁻¹ᵁ U).ι ≫ b)` using `by rw [e₀]; infer_instance`. Establish `: Flat ((b ⁻¹ᵁ U).ι ≫ b ≫ s)` using `by rw [← Category.assoc]; infer_instance`. Establish `hV : GlobalTheory.IsNormalScheme (b ⁻¹ᵁ U).toScheme` using `.of_isOpenImmersion ((b ⁻¹ᵁ U).ι ≫ b)`.

Take `⟨N, ν, hfin, hn, hpr, hfl, hν, hd⟩` from `GlobalTheory.ProjBlowup.exists_normal_model (b ≫ s) (b ⁻¹ᵁ U) hbs hV.pred fun x => by`. Establish `hy : ((b ⁻¹ᵁ U).ι ≫ b) x ∈ U` using `x.2`. Use `charZero_residueField V p hp s _ hy` as an intermediate fact. Conclude with `charZero_of_injective_ringHom (((b ⁻¹ᵁ U).ι ≫ b).residueFieldMap x).hom.injective`. Establish `hνb : IsIso ((ν ≫ b) ∣_ U)`.

Rewrite using `[morphismRestrict_comp]`. Conclude with `IsIso.comp_isIso' hν hbU`. Establish `: IsFinite ν` using `hfin`. Establish `: IsSeparated s`. Take `⟨n, i, hi, rfl⟩` from `hXp`.

Use `isProper_str V n` as an intermediate fact. Use `infer_instance`. Establish `: IsProper (b ≫ s)`. Take `⟨n, i, hi, e⟩` from `hbs`. Use `isProper_str V n` as an intermediate fact.

Rewrite using `[← e]`. Use `infer_instance`. Establish `: IsProper b` using `IsProper.of_comp b s`. Establish `hUne : (U : Set X).Nonempty`. Take `x` from `Classical.arbitrary X`.

Set `g₀ : Sp V` to `(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum V)`. Establish `hg₀s : g₀ ⤳ s x` using `(PrimeSpectrum.le_iff_specializes _ _).1 bot_le`. Take `⟨x', -, hx'⟩` from `Flat.generalizingMap s hg₀s`. Use `⟨x', ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x' ∈ X.basicOpen (p : Γ(X, ⊤))`.

Rewrite using `[← preimage_basicOpen_natCast p s]`. Express the relevant statement in the definitionally equal form `s x' ∈ (Sp V).basicOpen (p : Γ(Sp V, ⊤))`. Rewrite using `[hx']`. Establish `hp0 : (p : V) ≠ 0` using `fun h => by`. Establish `h' : ((p : V) : F) = 0` using `by rw [h]; rfl`.

Move the coercions through the operations in `at h'`. Conclude with `(Fact.out : p.Prime).ne_zero (by exact_mod_cast h')`. Establish `e : (p : Γ(Sp V, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of V)).inv (p : V)` using `by simp`. Rewrite using `[e, basicOpen_eq_of_affine]`. Conclude with `hp0`.

Establish `: Nonempty U` using `hUne.to_subtype`. Establish `: IsIntegral U.toScheme` using `isIntegral_of_isOpenImmersion U.ι`. Take `⟨j, hj, hjr⟩` from `GlobalTheory.ProjBlowup.exists_section_of_isIso_restrict (ν ≫ b) U`. Establish `hjd : Dense (Set.range j)` using `hd.mono hjr`. Establish `hirr : IsIrreducible (Set.range j)`.

Rewrite using `[← Set.image_univ]`. Conclude with `(IrreducibleSpace.isIrreducible_univ _).image j j.continuous.continuousOn`. Establish `: IrreducibleSpace N` using `(irreducibleSpace_def N).2 (by simpa [hjd.closure_eq] using hirr.closure)`. Establish `: GlobalTheory.IsNormalScheme N` using `.of_pred hn`. Establish `: IsReduced N` using `isReduced_of_isReduced_stalk N`.

Establish `: IsIntegral N` using `isIntegral_of_irreducibleSpace_of_isReduced N`. Conclude with `⟨X'', N, b, ν, hb.1, inferInstance, hn, hpr, hfl, inferInstance, hνb⟩`.
-/
theorem GlobalTheory.FlatModel.exists_normBlowup_off_basicOpen : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime],
    (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    IsProjOver s → Flat s → ∀ J : X.IdealSheafData, (∀ x ∈ J.support, x ∉ X.basicOpen (p : Γ(X, ⊤))) →
    ∃ (X'' X' : Scheme.{0}) (b : X'' ⟶ X) (ν : X' ⟶ X''), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) ∧
      IsIntegral X' ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ IsProjOver (ν ≫ b ≫ s) ∧ Flat (ν ≫ b ≫ s) ∧
      IsProper (ν ≫ b) ∧ IsIso ((ν ≫ b) ∣_ X.basicOpen (p : Γ(X, ⊤))) := by
  intro F _ _ V p _ hp X s hXi hXn hXp hXf J hJ
  have hDVR := (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V
    (Fact.out : p.Prime).ne_zero hp).1
  let U : X.Opens := X.basicOpen (p : Γ(X, ⊤))
  obtain ⟨X'', b, hb, hbs, hiso⟩ := GlobalTheory.ProjBlowup.exists_blowup s hXp J
  have hbU : IsIso (b ∣_ U) := hiso U fun x hx hJx => hJ x hJx hx
  have hN : GlobalTheory.IsNormalScheme X := .of_pred hXn
  have e₀ : (b ⁻¹ᵁ U).ι ≫ b = b ∣_ U ≫ U.ι := (morphismRestrict_ι b U).symm
  have : IsOpenImmersion ((b ⁻¹ᵁ U).ι ≫ b) := by rw [e₀]; infer_instance
  have : Flat ((b ⁻¹ᵁ U).ι ≫ b ≫ s) := by rw [← Category.assoc]; infer_instance
  have hV : GlobalTheory.IsNormalScheme (b ⁻¹ᵁ U).toScheme := .of_isOpenImmersion ((b ⁻¹ᵁ U).ι ≫ b)
  obtain ⟨N, ν, hfin, hn, hpr, hfl, hν, hd⟩ :=
    GlobalTheory.ProjBlowup.exists_normal_model (b ≫ s) (b ⁻¹ᵁ U) hbs hV.pred fun x => by
      have hy : ((b ⁻¹ᵁ U).ι ≫ b) x ∈ U := x.2
      have := charZero_residueField V p hp s _ hy
      exact charZero_of_injective_ringHom (((b ⁻¹ᵁ U).ι ≫ b).residueFieldMap x).hom.injective
  have hνb : IsIso ((ν ≫ b) ∣_ U) := by
    rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hbU
  have : IsFinite ν := hfin
  have : IsSeparated s := by
    obtain ⟨n, i, hi, rfl⟩ := hXp
    have := isProper_str V n
    infer_instance
  have : IsProper (b ≫ s) := by
    obtain ⟨n, i, hi, e⟩ := hbs
    have := isProper_str V n
    rw [← e]
    infer_instance
  have : IsProper b := IsProper.of_comp b s

  have hUne : (U : Set X).Nonempty := by
    obtain x := Classical.arbitrary X
    let g₀ : Sp V := (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum V)
    have hg₀s : g₀ ⤳ s x := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    obtain ⟨x', -, hx'⟩ := Flat.generalizingMap s hg₀s
    refine ⟨x', ?_⟩
    change x' ∈ X.basicOpen (p : Γ(X, ⊤))
    rw [← preimage_basicOpen_natCast p s]
    change s x' ∈ (Sp V).basicOpen (p : Γ(Sp V, ⊤))
    rw [hx']
    have hp0 : (p : V) ≠ 0 := fun h => by
      have h' : ((p : V) : F) = 0 := by rw [h]; rfl
      push_cast at h'
      exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h')
    have e : (p : Γ(Sp V, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of V)).inv (p : V) := by simp
    rw [e, basicOpen_eq_of_affine]
    exact hp0
  have : Nonempty U := hUne.to_subtype
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨j, hj, hjr⟩ := GlobalTheory.ProjBlowup.exists_section_of_isIso_restrict (ν ≫ b) U
  have hjd : Dense (Set.range j) := hd.mono hjr
  have hirr : IsIrreducible (Set.range j) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image j j.continuous.continuousOn
  have : IrreducibleSpace N := (irreducibleSpace_def N).2 (by simpa [hjd.closure_eq] using hirr.closure)
  have : GlobalTheory.IsNormalScheme N := .of_pred hn
  have : IsReduced N := isReduced_of_isReduced_stalk N
  have : IsIntegral N := isIntegral_of_irreducibleSpace_of_isReduced N
  exact ⟨X'', N, b, ν, hb.1, inferInstance, hn, hpr, hfl, inferInstance, hνb⟩
