import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeLinearFormNonnegStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionRankBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRegularFunctionTraitOrderStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrderCompatibleStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TorRef

/- English proof (translation)
Use `choose U hz f hreg hord using fun z => GlobalTheory.T.exists_regular_function_trait_order Z Cn φ hC hL z`. Establish `hassoc : ∀ x x' : Z.X, Associated (resG Z.X (inf_le_left : U x ⊓ U x' ≤ U x) (f x)) (resG Z.X (inf_le_right : U x ⊓ U x' ≤ U x') (f x'))` using `fun x x' => by`. Use `((hreg x).resG _).associated_of_germ ((hreg x').resG _) fun y hy => ?_` and prove the remaining obligations. Rewrite using `[germ_resG, germ_resG]`. Establish `hy1 : y ∈ U x` using `(Opens.mem_inf.1 hy).1`.

Establish `hy2 : y ∈ U x'` using `(Opens.mem_inf.1 hy).2`. Take `⟨u, hu⟩` from `GlobalTheory.T.trait_order_compatible Z Cn φ hC _ _ _ _ (hreg x) (hreg x') (hord x) (hord x') y hy1 hy2`. Conclude with `(Ideal.span_singleton_mul_right_unit u.isUnit _).symm.trans (congrArg (fun a => Ideal.span {a}) hu)`. Set `BD : EffCartierData Z.X` to `{ ι := Z.X U := U f := f cover := eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hz x⟩ regular := hreg assoc := hassoc }`. Use `⟨BD, fun W _ _ _ hW ϖ hϖ χ t m P hχ be hbe hmon => ?_⟩` and prove the remaining obligations.

Take `⟨n, hn, ha⟩` from `hord (χ (closedPoint W)) W hW ϖ hϖ χ t m P hχ be hbe hmon (hz _)`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Establish `hs : FinalTheorems.stalkId BD.idealSheaf (χ (closedPoint W)) = Ideal.span {(Z.X.presheaf.germ _ _ (hz (χ (closedPoint W)))).hom (f (χ (closedPoint W)))}` using `BD.stalkId_idealSheaf (χ (closedPoint W)) _ (hz _)`. Rewrite using `[idlAlong, hs, Ideal.map_span, Set.image_singleton]`. Take `⟨u, hu⟩` from `ha`.

Conclude with `(Ideal.span_singleton_mul_right_unit u.isUnit _).symm.trans (congrArg (fun a => Ideal.span {a}) hu)`.
-/
theorem exists_isPhiDiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)) (hC : HasCones Cn Z)
    (hL : HasLinForms Cn φ) : ∃ BD, IsPhiDiv φ Z BD := by
  choose U hz f hreg hord using fun z => GlobalTheory.T.exists_regular_function_trait_order Z Cn φ hC hL z
  have hassoc : ∀ x x' : Z.X, Associated (resG Z.X (inf_le_left : U x ⊓ U x' ≤ U x) (f x))
      (resG Z.X (inf_le_right : U x ⊓ U x' ≤ U x') (f x')) := fun x x' => by
    refine ((hreg x).resG _).associated_of_germ ((hreg x').resG _) fun y hy => ?_
    rw [germ_resG, germ_resG]
    have hy1 : y ∈ U x := (Opens.mem_inf.1 hy).1
    have hy2 : y ∈ U x' := (Opens.mem_inf.1 hy).2
    obtain ⟨u, hu⟩ := GlobalTheory.T.trait_order_compatible Z Cn φ hC _ _ _ _ (hreg x) (hreg x') (hord x) (hord x') y hy1 hy2
    exact (Ideal.span_singleton_mul_right_unit u.isUnit _).symm.trans (congrArg (fun a => Ideal.span {a}) hu)
  let BD : EffCartierData Z.X :=
    { ι := Z.X
      U := U
      f := f
      cover := eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hz x⟩
      regular := hreg
      assoc := hassoc }
  refine ⟨BD, fun W _ _ _ hW ϖ hϖ χ t m P hχ be hbe hmon => ?_⟩
  obtain ⟨n, hn, ha⟩ := hord (χ (closedPoint W)) W hW ϖ hϖ χ t m P hχ be hbe hmon (hz _)
  refine ⟨n, hn, ?_⟩
  have hs : FinalTheorems.stalkId BD.idealSheaf (χ (closedPoint W)) =
      Ideal.span {(Z.X.presheaf.germ _ _ (hz (χ (closedPoint W)))).hom (f (χ (closedPoint W)))} :=
    BD.stalkId_idealSheaf (χ (closedPoint W)) _ (hz _)
  rw [idlAlong, hs, Ideal.map_span, Set.image_singleton]
  obtain ⟨u, hu⟩ := ha
  exact (Ideal.span_singleton_mul_right_unit u.isUnit _).symm.trans (congrArg (fun a => Ideal.span {a}) hu)

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Z g φs hg hfan hC a b`. Establish `hC' : HasCones (ConeZr E g φs) Z`. Introduce `z`. Take `⟨R, i1, i2, i3, ξ, t, m, P, k, γ, hcn, hz, het, hfu, hti, hcn', hin⟩` from `hC z`. Conclude with `⟨R, i1, i2, i3, ξ, t, m, P, k, γ, hcn, hz, het, hfu, hti, ⟨hcn', inferInstance, (GlobalTheory.T.torsion_rank_bound Z R ξ t m P hcn het hti).trans hg⟩, hin⟩`.

Use `exists_isPhiDiv Z _ _ hC' ?_` and prove the remaining obligations. Introduce `X _ _ _ m γ ⟨hcone, hfree, hrank⟩`. Use `letI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X`. Take `⟨ℓ, hℓ⟩` from `GlobalTheory.T.cone_linear_form_nonneg g φs X hfan hrank m γ hcone`. Use `⟨b • ℓ, fun be hs cc hc hb => ?_⟩` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `hℓ be hs cc hc hb`. Use `⟨by simpa using mul_nonneg (Int.natCast_nonneg b) h1, ?_⟩` and prove the remaining obligations. Rewrite using `[InvFun.evalZ_comb, InvFun.evalZ_comb, InvFun.evalZ, InvFun.eval_resInt]`. Rewrite `h2` using `[InvFun.evalZ]`. Rewrite using `[← h2]`.

Simplify using the standard rewrite rules.
-/
theorem phiDivZSt : PhiDivZSt := by
  intro E _ _ _ H D l Xo c Z g φs hg hfan hC a b
  have hC' : HasCones (ConeZr E g φs) Z := by
    intro z
    obtain ⟨R, i1, i2, i3, ξ, t, m, P, k, γ, hcn, hz, het, hfu, hti, hcn', hin⟩ := hC z
    exact ⟨R, i1, i2, i3, ξ, t, m, P, k, γ, hcn, hz, het, hfu, hti,
      ⟨hcn', inferInstance, (GlobalTheory.T.torsion_rank_bound Z R ξ t m P hcn het hti).trans hg⟩, hin⟩
  refine exists_isPhiDiv Z _ _ hC' ?_
  intro X _ _ _ m γ ⟨hcone, hfree, hrank⟩
  letI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.cone_linear_form_nonneg g φs X hfan hrank m γ hcone
  refine ⟨b • ℓ, fun be hs cc hc hb => ?_⟩
  obtain ⟨h1, h2⟩ := hℓ be hs cc hc hb
  refine ⟨by simpa using mul_nonneg (Int.natCast_nonneg b) h1, ?_⟩
  rw [InvFun.evalZ_comb, InvFun.evalZ_comb, InvFun.evalZ, InvFun.eval_resInt]
  rw [InvFun.evalZ] at h2
  rw [← h2]
  simp

end GlobalTheory.TorRef
