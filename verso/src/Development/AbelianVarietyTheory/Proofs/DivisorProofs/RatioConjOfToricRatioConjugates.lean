import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueTiedOfIsToricElt
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassTermBoundBetaOfToricDenominator
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.HeckeGal GlobalTheory.ToricDenom
open Cardinal

namespace GlobalTheory.ToricRatioBridge

abbrev algC : Subfield ℂ := (algebraicClosure ℚ ℂ).toSubfield

/- English proof (translation)
The claim follows from `mem_algebraicClosure_iff`.
-/
theorem mem_algC {z : ℂ} : z ∈ algC ↔ IsAlgebraic ℚ z := mem_algebraicClosure_iff

/- English proof (translation)
Set `M : Subfield ℂ` to `algC`. Set `H : Subgroup (Af E)ˣ` to `M.toSubmonoid.units.comap (finPart χ)`. Establish `hH : ∀ y, y ∈ H ↔ (finPart χ y : ℂ) ∈ M` using `fun y => ⟨fun h => h.1, fun h => (Submonoid.mem_units_iff _ _).2 ⟨h, by rw [Units.val_inv_eq_inv_val]; exact M.inv_mem h⟩⟩`. Establish `hE : ∀ (σ : E →+* ℂ) (x : E), σ x ∈ M` using `fun σ x => mem_algC.2 ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom).isAlgebraic`. Establish `hle : princ ⊔ hatOUnits c ≤ H`.

Use `sup_le ?_ fun u h => (hH u).2 (by rw [hu u h]; exact one_mem M)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Rewrite using `[hH, eq_inv_of_mul_eq_one_left (finPart_mul_inf χ k), Units.val_inv_eq_inv_val, (hasInfRatio_iff χ φ m).1 hm k]`. Conclude with `inv_mem (prod_mem fun i _ => zpow_mem (div_mem (hE _ _) (hE ((starRingEnd ℂ).comp (φ i)) _)) _)`. Set `p : PicO c →* (Af E)ˣ ⧸ H` to `QuotientGroup.map _ _ (MonoidHom.id _) hle`.

Establish `: Finite ((Af E)ˣ ⧸ H)` using `Finite.of_surjective p fun q => by`. Take `⟨y, rfl⟩` from `QuotientGroup.mk_surjective q`. Conclude with `⟨QuotientGroup.mk y, rfl⟩`. Establish `hn` using `pow_card_eq_one' (G := (Af E)ˣ ⧸ H) (x := (QuotientGroup.mk y))`. Rewrite `hn` using `[← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hH, map_pow, Units.val_pow_eq_pow_val]`.

Conclude with `IsAlgebraic.of_pow Nat.card_pos (mem_algC.1 hn)`.
-/
theorem isAlgebraic_finPart {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {m : I → ℤ}
    {χ : HChar E} (hm : HasInf χ φ m) {c : Ideal (OF E)} [Finite (PicO c)] (hu : ∀ y ∈ hatOUnits c, finPart χ y = 1)
    (y : (Af E)ˣ) : IsAlgebraic ℚ (finPart χ y : ℂ) := by
  let M : Subfield ℂ := algC
  let H : Subgroup (Af E)ˣ := M.toSubmonoid.units.comap (finPart χ)
  have hH : ∀ y, y ∈ H ↔ (finPart χ y : ℂ) ∈ M := fun y =>
    ⟨fun h => h.1, fun h => (Submonoid.mem_units_iff _ _).2 ⟨h, by rw [Units.val_inv_eq_inv_val]; exact M.inv_mem h⟩⟩
  have hE : ∀ (σ : E →+* ℂ) (x : E), σ x ∈ M := fun σ x =>
    mem_algC.2 ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom).isAlgebraic
  have hle : princ ⊔ hatOUnits c ≤ H := by
    refine sup_le ?_ fun u h => (hH u).2 (by rw [hu u h]; exact one_mem M)
    rintro _ ⟨k, rfl⟩
    rw [hH, eq_inv_of_mul_eq_one_left (finPart_mul_inf χ k), Units.val_inv_eq_inv_val, (hasInfRatio_iff χ φ m).1 hm k]
    exact inv_mem (prod_mem fun i _ => zpow_mem (div_mem (hE _ _) (hE ((starRingEnd ℂ).comp (φ i)) _)) _)
  let p : PicO c →* (Af E)ˣ ⧸ H := QuotientGroup.map _ _ (MonoidHom.id _) hle
  have : Finite ((Af E)ˣ ⧸ H) := Finite.of_surjective p fun q => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk y, rfl⟩
  have hn := pow_card_eq_one' (G := (Af E)ˣ ⧸ H) (x := (QuotientGroup.mk y))
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hH, map_pow, Units.val_pow_eq_pow_val] at hn
  exact IsAlgebraic.of_pow Nat.card_pos (mem_algC.1 hn)

/- English proof (translation)
Set `_ : Algebra Ω ℂ` to `j.toAlgebra`. Establish `: CharZero Ω` using `RingHom.charZero j`. Establish `: IsScalarTower ℚ Ω ℂ` using `IsScalarTower.of_algebraMap_eq fun q => (map_ratCast j q).symm`. Establish `hi : IsIntegral Ω z` using `(hz.isIntegral).tower_top`. Take `⟨x, hx⟩` from `minpoly.mem_range_of_degree_eq_one Ω z (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hi))`.

Conclude with `⟨x, hx⟩`.
-/
theorem exists_eq_of_isAlgebraic {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* ℂ) {z : ℂ} (hz : IsAlgebraic ℚ z) :
    ∃ x : Ω, j x = z := by
  let _ : Algebra Ω ℂ := j.toAlgebra
  have : CharZero Ω := RingHom.charZero j
  have : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun q => (map_ratCast j q).symm
  have hi : IsIntegral Ω z := (hz.isIntegral).tower_top
  obtain ⟨x, hx⟩ := minpoly.mem_range_of_degree_eq_one Ω z
    (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hi))
  exact ⟨x, hx⟩

/- English proof (translation)
Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Establish `hx : (x : H.E) ∈ Algebra.adjoin ℚ {H.sqrtMinusD}`. Establish `h1 : IsIntegral ℚ H.sqrtMinusD` using `Algebra.IsIntegral.isIntegral _`. Establish `: (x : H.E) ∈ IntermediateField.adjoin ℚ {H.sqrtMinusD}` using `x.2`. Rewrite `this` using `[← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h1.isAlgebraic]`.

Conclude with `this`. Establish `hle : Algebra.adjoin ℚ {H.sqrtMinusD} ≤ AlgHom.equalizer f.toRatAlgHom g.toRatAlgHom` using `Algebra.adjoin_le (Set.singleton_subset_iff.2 h)`. Use `show f (x : H.E) = g (x : H.E)`. Conclude with `hle hx`.
-/
theorem comp_eq_of_sqrt {R : Ranks} (H : Host R) (f g : H.E →+* ℂ) (h : f H.sqrtMinusD = g H.sqrtMinusD) :
    f.comp (algebraMap H.K H.E) = g.comp (algebraMap H.K H.E) := by
  refine RingHom.ext fun x => ?_
  have hx : (x : H.E) ∈ Algebra.adjoin ℚ {H.sqrtMinusD} := by
    have h1 : IsIntegral ℚ H.sqrtMinusD := Algebra.IsIntegral.isIntegral _
    have : (x : H.E) ∈ IntermediateField.adjoin ℚ {H.sqrtMinusD} := x.2
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h1.isAlgebraic] at this
    exact this
  have hle : Algebra.adjoin ℚ {H.sqrtMinusD} ≤ AlgHom.equalizer f.toRatAlgHom g.toRatAlgHom :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 h)
  show f (x : H.E) = g (x : H.E)
  exact hle hx

/- English proof (translation)
The claim follows from `Units.ext (FiniteAdeleRing.ext _ fun P => (GlobalTheory.CharTransport.locMap_eq K E P _).symm)`.
-/
theorem upIdele_eq (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (t : (Af K)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.upIdele K E t = Units.map (GlobalTheory.AdeleBaseChange.adMap K E).toMonoidHom t :=
  Units.ext (FiniteAdeleRing.ext _ fun P => (GlobalTheory.CharTransport.locMap_eq K E P _).symm)

/- English proof (translation)
Establish `hK : #K ≤ ℵ₀`. Simplify `Algebra.IsAlgebraic.cardinalMk_le_max ℚ K` using `[Cardinal.mkRat]`. Establish `: Algebra.IsAlgebraic K Ω` using `IsAlgClosure.isAlgebraic`. Rewrite using `[← Cardinal.mk_le_aleph0_iff]`. Conclude with `(Algebra.IsAlgebraic.cardinalMk_le_max K Ω).trans (max_le hK le_rfl)`.
-/
theorem countable_of_isAlgClosure (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    Countable Ω := by
  have hK : #K ≤ ℵ₀ := by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  rw [← Cardinal.mk_le_aleph0_iff]
  exact (Algebra.IsAlgebraic.cardinalMk_le_max K Ω).trans (max_le hK le_rfl)

end GlobalTheory.ToricRatioBridge

namespace GlobalTheory.ToricRatioBridge

open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (ToricRatioConjugates IsSymbol classOf conjChar)

/- English proof (translation)
Introduce `R H I _ φ s κ 𝔣 χ hD Ω _ _ _ j τ₀ hj art ha T₀ hT₀ h0 Q hQ hfin T hT`. Establish `: IsCMField H.E` using `H.isCMField_hostE`. Establish `hU : UnramFin H.E` using `GlobalTheory.ToricDenomBridge.host_unramFin H`. Set `ι : H.K →+* ℂ` to `(φ τ₀).comp (algebraMap H.K H.E)`. Establish `hι : ∀ i, (φ i).comp (algebraMap H.K H.E) = ι` using `fun i => comp_eq_of_sqrt H _ _ (hD.2.1 i τ₀)`.

Set `δ : H.K` to `⟨H.sqrtMinusD, H.sqd_mem_K⟩`. Establish `hδ : δ ^ 2 = -(H.d : H.K)` using `Subtype.ext (by push_cast; exact H.sqrtMinusD_sq)`. Establish `hK2 : Module.finrank ℚ H.K = 2` using `H.finrank_K`. Take `⟨T₀', Tw, hT₀', -, hTw, halg, hconj⟩` from `hG H.E H.K H.d δ ι I φ s κ 𝔣 Q χ hU hK2 H.hyp.2.1.pos hδ hD.1 hι hD.2.2.1 hD.2.2.2.1 hD.2.2.2.2.1 hQ hD.2.2.2.2.2`. Establish `h𝔣 : condQ 𝔣 ∅ = 𝔣` using `by simp [condQ]`.

Establish `hT₀'' : IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀'` using `by rw [h𝔣]; exact hT₀'`. Establish `e0 : T₀' = T₀` using `hT₀''.unique hT₀`. Substitute `e0` using the available equality. Set `up : (PicO (condQ 𝔣 Q) →* Ωˣ) → (PicO (condQ 𝔣 Q) →* ℂˣ)` to `fun ψ => (Units.map j.toMonoidHom).comp ψ`. Establish `hsum : ∀ ψ', Tw ψ' = ∑ᶠ q, ((ψ' q : ℂˣ) : ℂ)⁻¹ * T q` using `fun ψ' => by`.

Take `⟨_, S, hS, e⟩` from `hTw ψ'`. Rewrite using `[e]`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Take `⟨S', hS', e'⟩` from `hT q`. Rewrite using `[e', mul_assoc, (hS q).unique hS']`.

Both sides reduce to the same expression. Establish `hΩ : IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed H.K`. Use `choose ρ hρ using fun ψ => exists_eq_of_isAlgebraic j (halg (up ψ))`. Use `⟨ρ, fun ψ => by rw [hρ, hsum]; rfl, fun g hgE hgl t ht ψ => ?_⟩` and prove the remaining obligations. Establish `: Countable Ω` using `countable_of_isAlgClosure H.K Ω`.

Take `⟨g', hg'⟩` from `GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq j (j.comp g.toRingEquiv.toRingHom)`. Establish `hfix : ∀ z : ℂ, IsAlgebraic ℚ z → (∀ x, j x = z → g x = x) → g' z = z` using `fun z hz hx => by`. Take `⟨x, rfl⟩` from `exists_eq_of_isAlgebraic j hz`. Rewrite using `[hg']`. Conclude with `congrArg j (hx x rfl)`.

Establish `hφ : ∀ i (x : H.E), IsAlgebraic ℚ (φ i x)` using `fun i x => ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map (φ i).toRatAlgHom).isAlgebraic`. Establish `: Finite (PicO (condQ 𝔣 ∅))` using `hT₀.1`. Establish `hl : ∀ y, IsAlgebraic ℚ (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s y)` using `fun y => by`. Establish `h1` using `isAlgebraic_finPart hD.2.2.2.2.2.2.2.1 (c := condQ 𝔣 ∅) (OrderUnits.finPart_eq_one H.E I φ hD.1 s κ 𝔣 ∅ χ hU hD.2.2.2.2.1 (fun _ h => absurd h (Finset.notMem_empty _)) hD.2.2.2.2.2) y`. Use `mem_algC.1 (mul_mem (mem_algC.2 h1) ?_)` and prove the remaining obligations.

Rewrite using `[Complex.ofReal_pow]`. Conclude with `pow_mem (GlobalTheory.ToricRational.modF_mem _ y) s`. Establish `hσ : ∀ x, j (g x) = g' (j x)` using `fun x => (hg' x).symm`. Establish `hsym : IsSymbol art t g` using `by rw [IsSymbol, ht, map_inv, inv_inv]`. Take `⟨e, -⟩` from `hconj Ω j art (RingHom.ext hj) ha g' g t (fun i x => hfix _ (hφ i x) fun x' hx' => hgE x' i x hx') (fun y => hfix _ (hl y) fun x' hx' => hgl x' y hx') hσ hsym (up ψ)`.

Establish `hc : conjChar g' (up ψ) = up ((Units.map g.toRingEquiv.toMonoidHom).comp ψ)` using `MonoidHom.ext fun q => Units.ext (hg' _)`. Establish `hcls : classOf H.K (condQ 𝔣 Q) t = QuotientGroup.mk (GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.upIdele H.K H.E t)`. Rewrite using `[classOf, upIdele_eq]`. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[hσ, hρ, e, hc, hcls, map_mul, map_inv₀, hρ]`.

Both sides reduce to the same expression.
-/
theorem ratioConj_of_toricRatioConjugates (hG : ToricRatioConjugates) : GlobalTheory.ToricRational.RatioConj := by
  intro R H I _ φ s κ 𝔣 χ hD Ω _ _ _ j τ₀ hj art ha T₀ hT₀ h0 Q hQ hfin T hT
  have : IsCMField H.E := H.isCMField_hostE
  have hU : UnramFin H.E := GlobalTheory.ToricDenomBridge.host_unramFin H
  let ι : H.K →+* ℂ := (φ τ₀).comp (algebraMap H.K H.E)
  have hι : ∀ i, (φ i).comp (algebraMap H.K H.E) = ι := fun i => comp_eq_of_sqrt H _ _ (hD.2.1 i τ₀)
  let δ : H.K := ⟨H.sqrtMinusD, H.sqd_mem_K⟩
  have hδ : δ ^ 2 = -(H.d : H.K) := Subtype.ext (by push_cast; exact H.sqrtMinusD_sq)
  have hK2 : Module.finrank ℚ H.K = 2 := H.finrank_K
  obtain ⟨T₀', Tw, hT₀', -, hTw, halg, hconj⟩ := hG H.E H.K H.d δ ι I φ s κ 𝔣 Q χ hU hK2 H.hyp.2.1.pos hδ hD.1 hι
    hD.2.2.1 hD.2.2.2.1 hD.2.2.2.2.1 hQ hD.2.2.2.2.2
  have h𝔣 : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]
  have hT₀'' : IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀' := by rw [h𝔣]; exact hT₀'
  have e0 : T₀' = T₀ := hT₀''.unique hT₀
  subst e0
  let up : (PicO (condQ 𝔣 Q) →* Ωˣ) → (PicO (condQ 𝔣 Q) →* ℂˣ) := fun ψ => (Units.map j.toMonoidHom).comp ψ
  have hsum : ∀ ψ', Tw ψ' = ∑ᶠ q, ((ψ' q : ℂˣ) : ℂ)⁻¹ * T q := fun ψ' => by
    obtain ⟨_, S, hS, e⟩ := hTw ψ'
    rw [e]
    refine finsum_congr fun q => ?_
    obtain ⟨S', hS', e'⟩ := hT q
    rw [e', mul_assoc, (hS q).unique hS']
    rfl
  have hΩ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed H.K
  choose ρ hρ using fun ψ => exists_eq_of_isAlgebraic j (halg (up ψ))
  refine ⟨ρ, fun ψ => by rw [hρ, hsum]; rfl, fun g hgE hgl t ht ψ => ?_⟩
  have : Countable Ω := countable_of_isAlgClosure H.K Ω
  obtain ⟨g', hg'⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq j (j.comp g.toRingEquiv.toRingHom)
  have hfix : ∀ z : ℂ, IsAlgebraic ℚ z → (∀ x, j x = z → g x = x) → g' z = z := fun z hz hx => by
    obtain ⟨x, rfl⟩ := exists_eq_of_isAlgebraic j hz
    rw [hg']
    exact congrArg j (hx x rfl)
  have hφ : ∀ i (x : H.E), IsAlgebraic ℚ (φ i x) := fun i x =>
    ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map (φ i).toRatAlgHom).isAlgebraic
  have : Finite (PicO (condQ 𝔣 ∅)) := hT₀.1
  have hl : ∀ y, IsAlgebraic ℚ (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s y) := fun y => by
    have h1 := isAlgebraic_finPart hD.2.2.2.2.2.2.2.1 (c := condQ 𝔣 ∅)
      (OrderUnits.finPart_eq_one H.E I φ hD.1 s κ 𝔣 ∅ χ hU hD.2.2.2.2.1 (fun _ h => absurd h (Finset.notMem_empty _))
        hD.2.2.2.2.2) y
    refine mem_algC.1 (mul_mem (mem_algC.2 h1) ?_)
    rw [Complex.ofReal_pow]
    exact pow_mem (GlobalTheory.ToricRational.modF_mem _ y) s
  have hσ : ∀ x, j (g x) = g' (j x) := fun x => (hg' x).symm
  have hsym : IsSymbol art t g := by rw [IsSymbol, ht, map_inv, inv_inv]
  obtain ⟨e, -⟩ := hconj Ω j art (RingHom.ext hj) ha g' g t (fun i x => hfix _ (hφ i x) fun x' hx' => hgE x' i x hx')
    (fun y => hfix _ (hl y) fun x' hx' => hgl x' y hx') hσ hsym (up ψ)
  have hc : conjChar g' (up ψ) = up ((Units.map g.toRingEquiv.toMonoidHom).comp ψ) :=
    MonoidHom.ext fun q => Units.ext (hg' _)
  have hcls : classOf H.K (condQ 𝔣 Q) t = QuotientGroup.mk (GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.upIdele H.K H.E t) := by
    rw [classOf, upIdele_eq]
  apply j.injective
  rw [hσ, hρ, e, hc, hcls, map_mul, map_inv₀, hρ]
  rfl

end GlobalTheory.ToricRatioBridge
