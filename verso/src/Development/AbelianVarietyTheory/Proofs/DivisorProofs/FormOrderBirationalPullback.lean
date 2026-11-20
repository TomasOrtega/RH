import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrders
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BirOrd

/- English proof (translation)
Introduce `k _ X Y _ _ p s _ hbij E' E hO n η hη`. Use `set φ := functionFieldMap s with hφdef`. Set `φe : X.functionField ≃+* Y.functionField` to `RingEquiv.ofBijective φ hbij`. Establish `hpc : φ.comp (Cartier.constFn p) = Cartier.constFn (s ≫ p)` using `EtaleKlt.functionFieldMap_comp_constFn p s`. Establish `hcc : (φe.symm : Y.functionField →+* X.functionField).comp (Cartier.constFn (s ≫ p)) = Cartier.constFn p`.

Use extensionality with `a`. Rewrite using `[← hpc]`. Conclude with `φe.symm_apply_apply _`. Set `Φ'` to `TopForm.formMap n (φe.symm : Y.functionField →+* X.functionField) hcc`. Establish `hinv : ∀ ξ : RatForms p n, Φ' (EtaleKlt.ratPull p s n ξ) = ξ`.

Introduce `ξ`. Establish `e0 : (φe.symm : Y.functionField →+* X.functionField).comp φ = RingHom.id _`. Use extensionality with `x`. Conclude with `φe.symm_apply_apply x`. Use `(TopForm.formMap_formMap φ (φe.symm : Y.functionField →+* X.functionField) (RingHom.id _) e0 hpc hcc (RingHom.id_comp _) ξ).trans ?_` and prove the remaining obligations.

Conclude with `TopForm.formMap_of_eq_id _ rfl _ ξ`. Set `ψ : E.ring →+* E'.ring` to `φ.restrict E.ring E'.ring fun x hx => (hO x).1 hx`. Establish `hψv : ∀ a, (ψ a : Y.functionField) = φ a` using `fun _ => rfl`. Establish `hψb : Function.Bijective ψ`. Use `⟨fun a b h => Subtype.ext (hbij.1 (by simpa [hψv] using congrArg Subtype.val h)), ?_⟩` and prove the remaining obligations.

Introduce `y`. Take `⟨x, hx⟩` from `hbij.2 (y : Y.functionField)`. Establish `hxE : x ∈ E.ring` using `(hO x).2 (hx ▸ y.2)`. Conclude with `⟨⟨x, hxE⟩, Subtype.ext hx⟩`. Set `eψ : E.ring ≃+* E'.ring` to `RingEquiv.ofBijective ψ hψb`.

Set `χ : E'.ring →+* E.ring` to `eψ.symm`. Establish `hc : ψ.comp E.const = E'.const`. Use extensionality with `a`. Conclude with `RingHom.congr_fun hpc a`. Establish `hc' : χ.comp E'.const = E.const`.

Use extensionality with `a`. Rewrite using `[← hc]`. Conclude with `congrArg Subtype.val (eψ.symm_apply_apply (E.const a))`. Establish `hχv : ∀ y, ((χ y : E.ring) : X.functionField) = φe.symm (y : Y.functionField)`. Introduce `y`.

Take `⟨x, rfl⟩` from `eψ.surjective y`. Establish `h1 : χ (eψ x) = x` using `eψ.symm_apply_apply x`. Rewrite using `[h1]`. Conclude with `(φe.symm_apply_apply (x : X.functionField)).symm`. Establish `hord : ∀ g : X.functionFieldˣ, E'.ord (Units.map φ.toMonoidHom g) = E.ord g`.

Introduce `g`. Take `⟨t, ht⟩` from `IsDiscreteValuationRing.exists_irreducible E.ring`. Conclude with `EtaleDiv.log_ordFrac_map E.ring E'.ring φ ψ hψv ht (ht.map eψ) g.ne_zero`. Establish `hfe : ∀ ω : Forms E.const n, IsFreeGen E.ring ω → IsFreeGen E'.ring (TopForm.formMap n ψ hc ω)` using `fun ω hω => EtaleDiv.isFreeGen_formMap (EtaleDiv.formallyEtale_of_bijective ψ hψb) hc hω`. Establish `hfe' : ∀ ω : Forms E'.const n, IsFreeGen E'.ring ω → IsFreeGen E.ring (TopForm.formMap n χ hc' ω)` using `fun ω hω => EtaleDiv.isFreeGen_formMap (EtaleDiv.formallyEtale_of_bijective χ eψ.symm.bijective) hc' hω`.

Establish `hτ : (E'.ring.subtype.comp ψ).comp E.const = Cartier.constFn (s ≫ p)`. Rewrite using `[RingHom.comp_assoc, hc]`. Both sides reduce to the same expression. Establish `key : ∀ ω : Forms E.const n, EtaleKlt.ratPull p s n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ψ hc ω)`. Introduce `ω`.

Establish `e : φ.comp E.ring.subtype = E'.ring.subtype.comp ψ`. Use extensionality with `x`. Both sides reduce to the same expression. Establish `k1` using `TopForm.formMap_formMap (D := n) E.ring.subtype φ _ e rfl hpc hτ ω`. Establish `k2` using `TopForm.formMap_formMap (D := n) ψ E'.ring.subtype _ rfl hc rfl hτ ω`.

Conclude with `k1.trans k2.symm`. Establish `hτ' : (E.ring.subtype.comp χ).comp E'.const = Cartier.constFn p`. Rewrite using `[RingHom.comp_assoc, hc']`. Both sides reduce to the same expression. Establish `key' : ∀ ω : Forms E'.const n, Φ' (E'.toRat n ω) = E.toRat n (TopForm.formMap n χ hc' ω)`.

Introduce `ω`. Establish `e : (φe.symm : Y.functionField →+* X.functionField).comp E'.ring.subtype = E.ring.subtype.comp χ`. Use extensionality with `y`. Conclude with `(hχv y).symm`. Establish `k1` using `TopForm.formMap_formMap (D := n) E'.ring.subtype (φe.symm : Y.functionField →+* X.functionField) _ e rfl hcc hτ' ω`.

Establish `k2` using `TopForm.formMap_formMap (D := n) χ E.ring.subtype _ rfl hc' rfl hτ' ω`. Conclude with `k1.trans k2.symm`. Establish `fwd : ∀ a, E.IsFormOrd η a → E'.IsFormOrd (EtaleKlt.ratPull p s n η) a`. Introduce and unpack `a ⟨ω, hω, g, hη', hg⟩`. Use `⟨_, hfe ω hω, Units.map φ.toMonoidHom g, ?_, (hord g).trans hg⟩` and prove the remaining obligations.

Rewrite using `[hη', map_smulₛₗ, key]`. Both sides reduce to the same expression. Establish `bwd : ∀ a, E'.IsFormOrd (EtaleKlt.ratPull p s n η) a → E.IsFormOrd η a`. Introduce and unpack `a ⟨ω, hω, f, hη', hf⟩`. Set `g : X.functionFieldˣ` to `Units.map (φe.symm : Y.functionField →+* X.functionField).toMonoidHom f`.

Establish `hgf : Units.map φ.toMonoidHom g = f`. Use `ext`. Conclude with `φe.apply_symm_apply (f : Y.functionField)`. Use `⟨_, hfe' ω hω, g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hinv η, hη', map_smulₛₗ, key']`.

Both sides reduce to the same expression. Rewrite using `[← hord g, hgf, hf]`. Establish `hne : EtaleKlt.ratPull p s n η ≠ 0`. Introduce `h0`. Apply `hη` to reduce the goal to its premises.

Rewrite using `[← hinv η, h0, map_zero]`. Distinguish the cases in `h : ∃ a, E.IsFormOrd η a`. Take `⟨a, ha⟩` from `h`. Rewrite using `[ha.formOrd_eq hη, (fwd a ha).formOrd_eq hne]`. Establish `h' : ¬ ∃ a, E'.IsFormOrd (EtaleKlt.ratPull p s n η) a` using `fun ⟨a, ha⟩ => h ⟨a, bwd a ha⟩`.

Rewrite using `[DivOver.formOrd, DivOver.formOrd, dif_neg h, dif_neg h']`.
-/
theorem formOrd_ratPull_of_over : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ (n : ℕ) (η : RatForms p n), η ≠ 0 → E'.formOrd (EtaleKlt.ratPull p s n η) = E.formOrd η := by
  intro k _ X Y _ _ p s _ hbij E' E hO n η hη
  set φ := functionFieldMap s with hφdef
  let φe : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective φ hbij
  have hpc : φ.comp (Cartier.constFn p) = Cartier.constFn (s ≫ p) :=
    EtaleKlt.functionFieldMap_comp_constFn p s
  have hcc : (φe.symm : Y.functionField →+* X.functionField).comp (Cartier.constFn (s ≫ p)) =
      Cartier.constFn p := by
    ext a
    rw [← hpc]
    exact φe.symm_apply_apply _

  let Φ' := TopForm.formMap n (φe.symm : Y.functionField →+* X.functionField) hcc
  have hinv : ∀ ξ : RatForms p n, Φ' (EtaleKlt.ratPull p s n ξ) = ξ := by
    intro ξ
    have e0 : (φe.symm : Y.functionField →+* X.functionField).comp φ = RingHom.id _ := by
      ext x
      exact φe.symm_apply_apply x
    refine (TopForm.formMap_formMap φ (φe.symm : Y.functionField →+* X.functionField)
      (RingHom.id _) e0 hpc hcc (RingHom.id_comp _) ξ).trans ?_
    exact TopForm.formMap_of_eq_id _ rfl _ ξ

  let ψ : E.ring →+* E'.ring := φ.restrict E.ring E'.ring fun x hx => (hO x).1 hx
  have hψv : ∀ a, (ψ a : Y.functionField) = φ a := fun _ => rfl
  have hψb : Function.Bijective ψ := by
    refine ⟨fun a b h => Subtype.ext (hbij.1 (by simpa [hψv] using congrArg Subtype.val h)), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := hbij.2 (y : Y.functionField)
    have hxE : x ∈ E.ring := (hO x).2 (hx ▸ y.2)
    exact ⟨⟨x, hxE⟩, Subtype.ext hx⟩
  let eψ : E.ring ≃+* E'.ring := RingEquiv.ofBijective ψ hψb
  let χ : E'.ring →+* E.ring := eψ.symm
  have hc : ψ.comp E.const = E'.const := by
    ext a
    exact RingHom.congr_fun hpc a
  have hc' : χ.comp E'.const = E.const := by
    ext a
    rw [← hc]
    exact congrArg Subtype.val (eψ.symm_apply_apply (E.const a))
  have hχv : ∀ y, ((χ y : E.ring) : X.functionField) = φe.symm (y : Y.functionField) := by
    intro y
    obtain ⟨x, rfl⟩ := eψ.surjective y
    have h1 : χ (eψ x) = x := eψ.symm_apply_apply x
    rw [h1]
    exact (φe.symm_apply_apply (x : X.functionField)).symm

  have hord : ∀ g : X.functionFieldˣ, E'.ord (Units.map φ.toMonoidHom g) = E.ord g := by
    intro g
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
    exact EtaleDiv.log_ordFrac_map E.ring E'.ring φ ψ hψv ht (ht.map eψ) g.ne_zero
  have hfe : ∀ ω : Forms E.const n, IsFreeGen E.ring ω →
      IsFreeGen E'.ring (TopForm.formMap n ψ hc ω) := fun ω hω =>
    EtaleDiv.isFreeGen_formMap (EtaleDiv.formallyEtale_of_bijective ψ hψb) hc hω
  have hfe' : ∀ ω : Forms E'.const n, IsFreeGen E'.ring ω →
      IsFreeGen E.ring (TopForm.formMap n χ hc' ω) := fun ω hω =>
    EtaleDiv.isFreeGen_formMap (EtaleDiv.formallyEtale_of_bijective χ eψ.symm.bijective) hc' hω
  have hτ : (E'.ring.subtype.comp ψ).comp E.const = Cartier.constFn (s ≫ p) := by
    rw [RingHom.comp_assoc, hc]
    rfl
  have key : ∀ ω : Forms E.const n,
      EtaleKlt.ratPull p s n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ψ hc ω) := by
    intro ω
    have e : φ.comp E.ring.subtype = E'.ring.subtype.comp ψ := by
      ext x
      rfl
    have k1 := TopForm.formMap_formMap (D := n) E.ring.subtype φ _ e rfl hpc hτ ω
    have k2 := TopForm.formMap_formMap (D := n) ψ E'.ring.subtype _ rfl hc rfl hτ ω
    exact k1.trans k2.symm
  have hτ' : (E.ring.subtype.comp χ).comp E'.const = Cartier.constFn p := by
    rw [RingHom.comp_assoc, hc']
    rfl
  have key' : ∀ ω : Forms E'.const n,
      Φ' (E'.toRat n ω) = E.toRat n (TopForm.formMap n χ hc' ω) := by
    intro ω
    have e : (φe.symm : Y.functionField →+* X.functionField).comp E'.ring.subtype =
        E.ring.subtype.comp χ := by
      ext y
      exact (hχv y).symm
    have k1 := TopForm.formMap_formMap (D := n) E'.ring.subtype
      (φe.symm : Y.functionField →+* X.functionField) _ e rfl hcc hτ' ω
    have k2 := TopForm.formMap_formMap (D := n) χ E.ring.subtype _ rfl hc' rfl hτ' ω
    exact k1.trans k2.symm
  have fwd : ∀ a, E.IsFormOrd η a → E'.IsFormOrd (EtaleKlt.ratPull p s n η) a := by
    rintro a ⟨ω, hω, g, hη', hg⟩
    refine ⟨_, hfe ω hω, Units.map φ.toMonoidHom g, ?_, (hord g).trans hg⟩
    rw [hη', map_smulₛₗ, key]
    rfl
  have bwd : ∀ a, E'.IsFormOrd (EtaleKlt.ratPull p s n η) a → E.IsFormOrd η a := by
    rintro a ⟨ω, hω, f, hη', hf⟩
    let g : X.functionFieldˣ := Units.map (φe.symm : Y.functionField →+* X.functionField).toMonoidHom f
    have hgf : Units.map φ.toMonoidHom g = f := by
      ext
      exact φe.apply_symm_apply (f : Y.functionField)
    refine ⟨_, hfe' ω hω, g, ?_, ?_⟩
    · rw [← hinv η, hη', map_smulₛₗ, key']
      rfl
    · rw [← hord g, hgf, hf]
  have hne : EtaleKlt.ratPull p s n η ≠ 0 := by
    intro h0
    apply hη
    rw [← hinv η, h0, map_zero]
  by_cases h : ∃ a, E.IsFormOrd η a
  · obtain ⟨a, ha⟩ := h
    rw [ha.formOrd_eq hη, (fwd a ha).formOrd_eq hne]
  · have h' : ¬ ∃ a, E'.IsFormOrd (EtaleKlt.ratPull p s n η) a :=
      fun ⟨a, ha⟩ => h ⟨a, bwd a ha⟩
    rw [DivOver.formOrd, DivOver.formOrd, dif_neg h, dif_neg h']

end GlobalTheory.BirOrd
