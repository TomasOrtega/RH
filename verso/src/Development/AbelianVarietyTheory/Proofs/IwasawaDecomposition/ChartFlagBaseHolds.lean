import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHoldsStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Cht.FlagBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact MonObj.comp_one e`. Consider the case `cons a L ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]`.
-/
theorem comp_listProd {B : Scheme.{0}} {G : Over B} [GrpObj G] {X Y : Over B} (e : X ⟶ Y) (L : List (Y ⟶ G)) :
    e ≫ L.prod = (L.map (e ≫ ·)).prod := by
  induction L with
  | nil => exact MonObj.comp_one e
  | cons a L ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

/- English proof (translation)
Take `⟨u, hu, hw⟩` from `h`. Establish `he : spMap (dualMap ψ) ≫ (tEpsG x).hom = (tEpsG (spMap ψ ≫ x)).hom` using `by show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ ≫ x`. Rewrite using `[← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]`. Use `congr 2`. Apply `RingHom.ext` to reduce the goal to its premises.

Introduce `r`. Apply the tactic sequence `ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`. Set `e : tEpsG (spMap ψ ≫ x) ⟶ tEpsG x` to `Over.homMk (spMap (dualMap ψ)) he`. Use `⟨fun i => e ≫ u i, fun i => ?_, ?_⟩` and prove the remaining obligations. Use `show spMap (dualMap ψ) ≫ (u i).left = spMap (epsMul (ψ (a i))) ≫ spMap (dualMap ψ) ≫ v i`.

Rewrite using `[hu i, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]`. Use `congr 2`. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `r`. Apply the tactic sequence `ext <;> simp [dualMap, epsMul, _root_.mul_comm]`.

Establish `hl : (List.ofFn fun i => e ≫ u i) = (List.ofFn u).map (e ≫ ·)`. Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression. Rewrite using `[hl, ← comp_listProd, Over.comp_left, hw]`. Both sides reduce to the same expression.
-/
theorem isCombAtG_bc {X : Scheme.{0}} (t : SAB H X) {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')
    {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) :
    IsCombAtG t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ v j) (fun j => ψ (a j)) (spMap (dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, hw⟩ := h
  have he : spMap (dualMap ψ) ≫ (tEpsG x).hom = (tEpsG (spMap ψ ≫ x)).hom := by
    show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ ≫ x
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let e : tEpsG (spMap ψ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap ψ)) he
  refine ⟨fun i => e ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMap ψ) ≫ (u i).left = spMap (epsMul (ψ (a i))) ≫ spMap (dualMap ψ) ≫ v i
    rw [hu i, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, epsMul, _root_.mul_comm]
  · have hl : (List.ofFn fun i => e ≫ u i) = (List.ofFn u).map (e ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [hl, ← comp_listProd, Over.comp_left, hw]
    rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ i`. Use `show spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ u τ i = spMap (dualMap (ψ.comp φ)) ≫ u τ i`. Rewrite using `[← Category.assoc, ← spMap_comp]`. Use `congr 2`. Apply `RingHom.ext` to reduce the goal to its premises.

Introduce `r`. Apply the tactic sequence `ext <;> simp [dualMap]`.
-/
theorem bc_bc {Dw : Datum H} {X : Scheme.{0}} {t : SAB H X} {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (u : Vecs Dw t R) : (u.bc φ).bc ψ = u.bc (ψ.comp φ) := by
  funext τ i
  show spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ u τ i = spMap (dualMap (ψ.comp φ)) ≫ u τ i
  rw [← Category.assoc, ← spMap_comp]
  congr 2
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap]

/- English proof (translation)
Establish `h' : Set.range w ⊆ Set.range hU.fromSpec` using `by rw [hU.range_fromSpec]; exact h`. Use `⟨(Spec.preimage (IsOpenImmersion.lift hU.fromSpec w h')).hom, ?_⟩` and prove the remaining obligations. Rewrite using `[spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]`.
-/
theorem exists_spMap_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {k : Type} [CommRing k]
    (w : Sp k ⟶ X) (h : Set.range w ⊆ (U : Set X)) : ∃ φ : Γ(X, U) →+* k, spMap φ ≫ hU.fromSpec = w := by
  have h' : Set.range w ⊆ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact h
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hU.fromSpec w h')).hom, ?_⟩
  rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

/- English proof (translation)
Introduce `E _ _ _ H Dw Xo p W Y i₀ Z k _ w`. Use `⟨fun hw => ?_, fun k' _ ψ u ⟨a, φ, hφ, hfr, hs⟩ => ?_⟩` and prove the remaining obligations. Establish `h0 : w (closedPoint k) ∈ ⋃ a, ((Z.U a).1 : Set Z.X)` using `Z.cover ▸ hw ⟨_, rfl⟩`. Take `⟨a, ha⟩` from `Set.mem_iUnion.1 h0`. Take `⟨φ, hφ⟩` from `exists_spMap_fromSpec (Z.U a).2 w (by`.

Introduce and unpack `_ ⟨q, rfl⟩`. Rewrite using `[show q = closedPoint k from Subsingleton.elim (α := PrimeSpectrum k) _ _])` and apply the resulting hypothesis. Establish `hφ' : spMap φ ≫ Z.chart a = w` using `hφ`. Establish `hfr` using `hF _ _ _ _ _ _ _ _ _ _ _ φ _ (Z.frame a)`. Rewrite `hfr` using `[← Category.assoc, hφ']`.

Use `⟨(Z.fr a).bc φ, a, φ, hφ', hfr, fun τ n _ i hi => ⟨Pi.single i 1, fun j hj => ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `Pi.single_eq_of_ne (fun e => by subst e; omega) _`. Conclude with `isCombAtG_single _ _ (fun j => (hfr.1 τ j).1) i`. Use `⟨a, ψ.comp φ, by rw [spMap_comp, Category.assoc, hφ], ?_, fun τ n hn i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, RingHom.comp_assoc]`.

Conclude with `hF _ _ _ _ _ _ _ _ _ _ _ ψ _ hfr`. Take `⟨cf, h0, hc⟩` from `hs τ n hn i hi`. Use `⟨fun j => ψ (cf j), fun j hj => (congrArg ψ (h0 j hj)).trans (map_zero ψ), ?_⟩` and prove the remaining obligations. Rewrite using `[← bc_bc, Category.assoc]`. Conclude with `isCombAtG_bc _ ψ hc`.
-/
theorem flagBase_of (hF : FrameBaseSt) : FlagBaseSt := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z k _ w
  refine ⟨fun hw => ?_, fun k' _ ψ u ⟨a, φ, hφ, hfr, hs⟩ => ?_⟩
  · have h0 : w (closedPoint k) ∈ ⋃ a, ((Z.U a).1 : Set Z.X) := Z.cover ▸ hw ⟨_, rfl⟩
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 h0
    obtain ⟨φ, hφ⟩ := exists_spMap_fromSpec (Z.U a).2 w (by
      rintro _ ⟨q, rfl⟩
      rwa [show q = closedPoint k from Subsingleton.elim (α := PrimeSpectrum k) _ _])
    have hφ' : spMap φ ≫ Z.chart a = w := hφ
    have hfr := hF _ _ _ _ _ _ _ _ _ _ _ φ _ (Z.frame a)
    rw [← Category.assoc, hφ'] at hfr
    refine ⟨(Z.fr a).bc φ, a, φ, hφ', hfr, fun τ n _ i hi => ⟨Pi.single i 1, fun j hj => ?_, ?_⟩⟩
    · exact Pi.single_eq_of_ne (fun e => by subst e; omega) _
    · exact isCombAtG_single _ _ (fun j => (hfr.1 τ j).1) i
  · refine ⟨a, ψ.comp φ, by rw [spMap_comp, Category.assoc, hφ], ?_, fun τ n hn i hi => ?_⟩
    · rw [Category.assoc, RingHom.comp_assoc]
      exact hF _ _ _ _ _ _ _ _ _ _ _ ψ _ hfr
    · obtain ⟨cf, h0, hc⟩ := hs τ n hn i hi
      refine ⟨fun j => ψ (cf j), fun j hj => (congrArg ψ (h0 j hj)).trans (map_zero ψ), ?_⟩
      rw [← bc_bc, Category.assoc]
      exact isCombAtG_bc _ ψ hc

/- English proof (translation)
The claim follows from `flagBase_of GlobalTheory.T.chart_frame_base_holds`.
-/
theorem flagBase : FlagBaseSt := flagBase_of GlobalTheory.T.chart_frame_base_holds

end GlobalTheory.LocM.Cht.FlagBase
