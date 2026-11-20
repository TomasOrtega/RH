import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.CoverNorm

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem appLE_apply_congr {X Z : Scheme.{0}} {a c : Z ⟶ X} (e : a = c) (U : X.Opens) (W : Z.Opens)
    (h₁ : W ≤ a ⁻¹ᵁ U) (h₂ : W ≤ c ⁻¹ᵁ U) (s : Γ(X, U)) : (a.appLE U W h₁).hom s = (c.appLE U W h₂).hom s := by
  subst e; rfl

/- English proof (translation)
Establish `h0 : t ≠ 0` using `h.ne_zero`. Rewrite using `[unitAt_iff ((map_ne_zero _).2 h0), ← map_inv₀]`. Conclude with `⟨ProjSpace.regAt_fnMap_of g hη h.regAt, ProjSpace.regAt_fnMap_of g hη h.inv.regAt⟩`.
-/
theorem unitAt_fnMap_of {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (g : Z ⟶ X)
    (hη : g (genericPoint Z) ⤳ genericPoint X) {x : Z} {t : X.functionField} (h : UnitAt (g x) t) :
    UnitAt x (SmallSec.fnMap g hη t) := by
  have h0 : t ≠ 0 := h.ne_zero
  rw [unitAt_iff ((map_ne_zero _).2 h0), ← map_inv₀]
  exact ⟨ProjSpace.regAt_fnMap_of g hη h.regAt, ProjSpace.regAt_fnMap_of g hη h.inv.regAt⟩

/- English proof (translation)
Introduce `F _ _ Y V V' b hb g hj hπ hg L f a l h`. Take `⟨r, hr, hu, hc, hfin⟩` from `h`. Establish `hgη : g (genericPoint V'.G) ⤳ genericPoint V.G` using `specializes_of_eq hg`. Use `set ψ := SmallSec.fnMap g hgη with hψ`. Take `⟨hη, e⟩` from `V.φ_eq_fnMap`.

Take `⟨hη', e'⟩` from `V'.φ_eq_fnMap`. Establish `hφ : ∀ t, V'.φ t = ψ (V.φ t)`. Introduce `t`. Rewrite using `[e', e, ← ProjSpace.fnMap_comp g V.π hgη hη (ProjSpace.comp_genericPoint_specializes _ _ hgη hη) t]`. Conclude with `ProjSpace.fnMap_congr hπ.symm _ _ _`.

Establish `hπx : ∀ x, V.π (g x) = V'.π x` using `fun x => by rw [← hπ]; rfl`. Establish `hch : ∀ (i : ((L.pull b hb).B.pull V'.j).ι), ∀ x ∈ ((L.pull b hb).B.pull V'.j).U i, g x ∈ (L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit)`. Introduce `i x hx`. Establish `h1` using `Set.mem_iInter.1 (InducedPull.chart_le L.B b V'.j i hx) PUnit.unit`. Establish `h2 : (V'.j ≫ b) x = V.j (g x)` using `by rw [hj]; rfl`.

Use `Set.mem_iInter.2 fun _ => ?_` and prove the remaining obligations. Use `show V.j (g x) ∈ L.B.U _`. Rewrite using `[← h2]`. Conclude with `h1`. Set `r' : ((L.pull b hb).B.pull V'.j).ι → V'.G.functionFieldˣ` to `fun i => Units.map ψ.toMonoidHom (r fun _ => i PUnit.unit PUnit.unit)`.

Establish `hr' : ∀ i, (r' i : V'.G.functionField) = ψ (r fun _ => i PUnit.unit PUnit.unit)` using `fun _ => rfl`. Use `⟨r', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Establish `h0 : genericPoint V.G ∈ (L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (L.B.pull V.j).U (fun _ => j PUnit.unit PUnit.unit)`. Rewrite using `[← hg]`.

Conclude with `⟨hch i _ hij.1, hch j _ hij.2⟩`. Establish `le : ((L.pull b hb).B.pull V'.j).U i ⊓ ((L.pull b hb).B.pull V'.j).U j ≤ g ⁻¹ᵁ ((L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (L.B.pull V.j).U (fun _ => j PUnit.unit PUnit.unit))` using `fun x hx => ⟨hch i x hx.1, hch j x hx.2⟩`. Rewrite using `[hr', hr', hr _ _ h0, map_mul, ← ProjSpace.fnOf_appLE g hgη le h0 hij]`. Use `congr 2`. Establish `k1` using `InducedPull.val_pull_g L.B V.j (fun _ => i PUnit.unit PUnit.unit) (fun _ => j PUnit.unit PUnit.unit) (InducedPull.inf_le _ _ _ _)`.

Establish `k2` using `InducedPull.val_pull_g (L.B.pull b) V'.j i j (InducedPull.inf_le _ _ _ _)`. Establish `k3` using `InducedPull.val_pull_g L.B b (i PUnit.unit) (j PUnit.unit) (InducedPull.inf_le _ _ _ _)`. Use `(congrArg _ k1).trans (k2.trans ?_).symm` and prove the remaining obligations. Use `(congrArg _ k3).trans ?_` and prove the remaining obligations. Rewrite using `[← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]`.

Conclude with `appLE_apply_congr hj _ _ _ _ _`. Introduce `i x hx`. Rewrite using `[hr', hφ, ← map_mul, ← hπx]`. Conclude with `unitAt_fnMap_of g hgη (hu _ _ (hch i x hx))`. Introduce `σ z y y' i e1 e2 hi`.

Set `z0 : CxPts (V.π ≫ Y.str) σ` to `⟨z.1 ≫ g, by rw [Category.assoc, ← Category.assoc g, hπ]; exact z.2⟩`. Set `y0` to `Points.PtsOver.map b hb _ y'`. Establish `e1' : y.1 = z0.1 ≫ V.π`. Rewrite using `[e1]`. Use `show z.1 ≫ V'.π = (z.1 ≫ g) ≫ V.π`.

Rewrite using `[Category.assoc, hπ]`. Establish `e2' : y0.1 = z0.1 ≫ V.j` using `by show y'.1 ≫ b = (z.1 ≫ g) ≫ V.j`. Rewrite using `[e2, Category.assoc, hj, Category.assoc]`. Establish `hi0 : under z0 ∈ (L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit)` using `hch i _ hi`. Establish `H` using `hc σ z0 y y0 (fun _ => i PUnit.unit PUnit.unit) e1' e2' hi0`.

Establish `hπ0 : V.π (under z0) = under y` using `by show _ = y.1 _`. Rewrite using `[e1']`. Both sides reduce to the same expression. Establish `hU` using `hu _ _ hi0`. Rewrite `hU` using `[hπ0]`.

Establish `hw : ((L.pull b hb).φ _).φ (i PUnit.unit) y' = (L.φ _).φ (i PUnit.unit PUnit.unit) y0` using `(L.φ _).pull_φ b hb (i PUnit.unit) y'`. Rewrite using `[H, hr', hφ, ← map_mul, hw, SmallSec.ratVal_eq_valAt z (ProjSpace.regAt_fnMap_of g hgη hU.regAt), SmallSec.ratVal_eq_valAt z0 hU.regAt, SmallSec.valAt_fnMap g hgη z.1 hU.regAt]`. Introduce `v e y z yt i e1 e2 hi`. Establish `e1' : (z ≫ g) ≫ V.π = y.1` using `by rw [Category.assoc, hπ, e1]`. Establish `e2' : spMap e.O.subtype ≫ (yt ≫ b) = (z ≫ g) ≫ V.j`.

Rewrite using `[← Category.assoc, e2, Category.assoc, hj, Category.assoc]`. Establish `hi' : ⊤ ≤ (yt ≫ b) ⁻¹ᵁ L.B.U (i PUnit.unit PUnit.unit)` using `fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit`. Establish `H` using `hfin v e y (z ≫ g) (yt ≫ b) (fun _ => i PUnit.unit PUnit.unit) e1' e2' hi'`. Establish `hmem : below (z ≫ g) ∈ (L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit)`. Establish `h1 : ((z ≫ g) ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U (i PUnit.unit PUnit.unit)`.

Rewrite using `[← e2']`. Conclude with `hi' (Set.mem_univ _)`. Conclude with `Set.mem_iInter.2 fun _ => h1`. Establish `hπ0 : V.π (below (z ≫ g)) = below y.1`. Rewrite using `[← e1']`.

Both sides reduce to the same expression. Establish `hU` using `hu _ _ hmem`. Rewrite `hU` using `[hπ0]`. Rewrite using `[H, hr', hφ, ← map_mul, SmallSec.valAt_fnMap g hgη z hU.regAt]`.
-/
theorem norms_pull : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (V' : Cover Y) (b : V'.X ⟶ V.X)
    (hb : b ≫ V.p = V'.p) (g : V'.G ⟶ V.G), V'.j ≫ b = g ≫ V.j → g ≫ V.π = V'.π →
    g (genericPoint V'.G) = genericPoint V.G → ∀ (L : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ)
    (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ), Norms V L f a l → Norms V' (L.pull b hb) f a l := by
  intro F _ _ Y V V' b hb g hj hπ hg L f a l h
  obtain ⟨r, hr, hu, hc, hfin⟩ := h
  have hgη : g (genericPoint V'.G) ⤳ genericPoint V.G := specializes_of_eq hg
  set ψ := SmallSec.fnMap g hgη with hψ
  obtain ⟨hη, e⟩ := V.φ_eq_fnMap
  obtain ⟨hη', e'⟩ := V'.φ_eq_fnMap
  have hφ : ∀ t, V'.φ t = ψ (V.φ t) := by
    intro t
    rw [e', e, ← ProjSpace.fnMap_comp g V.π hgη hη (ProjSpace.comp_genericPoint_specializes _ _ hgη hη) t]
    exact ProjSpace.fnMap_congr hπ.symm _ _ _
  have hπx : ∀ x, V.π (g x) = V'.π x := fun x => by rw [← hπ]; rfl
  have hch : ∀ (i : ((L.pull b hb).B.pull V'.j).ι), ∀ x ∈ ((L.pull b hb).B.pull V'.j).U i,
      g x ∈ (L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit) := by
    intro i x hx
    have h1 := Set.mem_iInter.1 (InducedPull.chart_le L.B b V'.j i hx) PUnit.unit
    have h2 : (V'.j ≫ b) x = V.j (g x) := by rw [hj]; rfl
    refine Set.mem_iInter.2 fun _ => ?_
    show V.j (g x) ∈ L.B.U _
    rw [← h2]
    exact h1
  let r' : ((L.pull b hb).B.pull V'.j).ι → V'.G.functionFieldˣ :=
    fun i => Units.map ψ.toMonoidHom (r fun _ => i PUnit.unit PUnit.unit)
  have hr' : ∀ i, (r' i : V'.G.functionField) = ψ (r fun _ => i PUnit.unit PUnit.unit) := fun _ => rfl
  refine ⟨r', ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h0 : genericPoint V.G ∈ (L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓
        (L.B.pull V.j).U (fun _ => j PUnit.unit PUnit.unit) := by
      rw [← hg]
      exact ⟨hch i _ hij.1, hch j _ hij.2⟩
    have le : ((L.pull b hb).B.pull V'.j).U i ⊓ ((L.pull b hb).B.pull V'.j).U j ≤
        g ⁻¹ᵁ ((L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (L.B.pull V.j).U (fun _ => j PUnit.unit PUnit.unit)) :=
      fun x hx => ⟨hch i x hx.1, hch j x hx.2⟩
    rw [hr', hr', hr _ _ h0, map_mul, ← ProjSpace.fnOf_appLE g hgη le h0 hij]
    congr 2
    have k1 := InducedPull.val_pull_g L.B V.j (fun _ => i PUnit.unit PUnit.unit) (fun _ => j PUnit.unit PUnit.unit)
      (InducedPull.inf_le _ _ _ _)
    have k2 := InducedPull.val_pull_g (L.B.pull b) V'.j i j (InducedPull.inf_le _ _ _ _)
    have k3 := InducedPull.val_pull_g L.B b (i PUnit.unit) (j PUnit.unit) (InducedPull.inf_le _ _ _ _)
    refine (congrArg _ k1).trans (k2.trans ?_).symm
    refine (congrArg _ k3).trans ?_
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_apply_congr hj _ _ _ _ _
  · intro i x hx
    rw [hr', hφ, ← map_mul, ← hπx]
    exact unitAt_fnMap_of g hgη (hu _ _ (hch i x hx))
  · intro σ z y y' i e1 e2 hi
    let z0 : CxPts (V.π ≫ Y.str) σ := ⟨z.1 ≫ g, by rw [Category.assoc, ← Category.assoc g, hπ]; exact z.2⟩
    let y0 := Points.PtsOver.map b hb _ y'
    have e1' : y.1 = z0.1 ≫ V.π := by
      rw [e1]
      show z.1 ≫ V'.π = (z.1 ≫ g) ≫ V.π
      rw [Category.assoc, hπ]
    have e2' : y0.1 = z0.1 ≫ V.j := by
      show y'.1 ≫ b = (z.1 ≫ g) ≫ V.j
      rw [e2, Category.assoc, hj, Category.assoc]
    have hi0 : under z0 ∈ (L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit) := hch i _ hi
    have H := hc σ z0 y y0 (fun _ => i PUnit.unit PUnit.unit) e1' e2' hi0
    have hπ0 : V.π (under z0) = under y := by
      show _ = y.1 _
      rw [e1']
      rfl
    have hU := hu _ _ hi0
    rw [hπ0] at hU
    have hw : ((L.pull b hb).φ _).φ (i PUnit.unit) y' = (L.φ _).φ (i PUnit.unit PUnit.unit) y0 :=
      (L.φ _).pull_φ b hb (i PUnit.unit) y'
    rw [H, hr', hφ, ← map_mul, hw, SmallSec.ratVal_eq_valAt z (ProjSpace.regAt_fnMap_of g hgη hU.regAt),
      SmallSec.ratVal_eq_valAt z0 hU.regAt, SmallSec.valAt_fnMap g hgη z.1 hU.regAt]
  · intro v e y z yt i e1 e2 hi
    have e1' : (z ≫ g) ≫ V.π = y.1 := by rw [Category.assoc, hπ, e1]
    have e2' : spMap e.O.subtype ≫ (yt ≫ b) = (z ≫ g) ≫ V.j := by
      rw [← Category.assoc, e2, Category.assoc, hj, Category.assoc]
    have hi' : ⊤ ≤ (yt ≫ b) ⁻¹ᵁ L.B.U (i PUnit.unit PUnit.unit) :=
      fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit
    have H := hfin v e y (z ≫ g) (yt ≫ b) (fun _ => i PUnit.unit PUnit.unit) e1' e2' hi'
    have hmem : below (z ≫ g) ∈ (L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit) := by
      have h1 : ((z ≫ g) ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U (i PUnit.unit PUnit.unit) := by
        rw [← e2']
        exact hi' (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hπ0 : V.π (below (z ≫ g)) = below y.1 := by
      rw [← e1']
      rfl
    have hU := hu _ _ hmem
    rw [hπ0] at hU
    rw [H, hr', hφ, ← map_mul, SmallSec.valAt_fnMap g hgη z hU.regAt]

end GlobalTheory.CoverNorm
