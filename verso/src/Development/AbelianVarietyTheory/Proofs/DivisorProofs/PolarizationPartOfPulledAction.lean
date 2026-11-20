import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiabelianExtensionDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrLiftOfGeometricPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionPolarizationPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationPartBaseChangeStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolPoint

open IsLocalRing

/- English proof (translation)
Establish `w : φ ≫ G.hom = (G''.hom ≫ g) ≫ f` using `by rw [h.1.1.w, Category.assoc]`. Set `φ'` to `h'.1.1.lift φ (G''.hom ≫ g) w`. Establish `e₁ : φ' ≫ ψ = φ` using `h'.1.1.lift_fst _ _ _`. Establish `e₂ : φ' ≫ G'.hom = G''.hom ≫ g` using `h'.1.1.lift_snd _ _ _`. Use `⟨φ', h'.1.cancel (h.1.congr rfl e₁.symm) e₂, fun a => ?_⟩` and prove the remaining obligations.

Apply `h'.1.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, e₁, h.2, Category.assoc, h'.2, ← Category.assoc, e₁]`. Rewrite using `[Category.assoc, e₂, Category.assoc, Over.w (i'.act a), e₂, ← Category.assoc, Over.w (i''.act a)]`.
-/
theorem actPull_cancel {O : Type} [CommRing O] {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'}
    [GrpObj G'] {G'' : Over S''} [GrpObj G''] {i : OAct O G} {i' : OAct O G'} {i'' : OAct O G''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {ψ : G'.left ⟶ G.left} {φ : G''.left ⟶ G.left} (h' : IsActPull i' i f ψ)
    (h : IsActPull i'' i (g ≫ f) φ) : ∃ φ' : G''.left ⟶ G'.left, IsActPull i'' i' g φ' := by
  have w : φ ≫ G.hom = (G''.hom ≫ g) ≫ f := by rw [h.1.1.w, Category.assoc]
  let φ' := h'.1.1.lift φ (G''.hom ≫ g) w
  have e₁ : φ' ≫ ψ = φ := h'.1.1.lift_fst _ _ _
  have e₂ : φ' ≫ G'.hom = G''.hom ≫ g := h'.1.1.lift_snd _ _ _
  refine ⟨φ', h'.1.cancel (h.1.congr rfl e₁.symm) e₂, fun a => ?_⟩
  apply h'.1.1.hom_ext
  · rw [Category.assoc, e₁, h.2, Category.assoc, h'.2, ← Category.assoc, e₁]
  · rw [Category.assoc, e₂, Category.assoc, Over.w (i'.act a), e₂, ← Category.assoc, Over.w (i''.act a)]

/- English proof (translation)
Use `letI := (ResidueField.map φ).toAlgebra`. Use `letI := ι.toAlgebra`. Establish `: Algebra.IsIntegral (ResidueField V) (ResidueField V')` using `⟨fun y => by`. Take `⟨b, rfl⟩` from `residue_surjective y`. Take `⟨p, hp, hpb⟩` from `hf.to_isIntegral b`.

Use `⟨p.map (residue V), hp.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`. Establish `e : (algebraMap (ResidueField V) (ResidueField V')).comp (residue V) = (residue V').comp φ` using `ResidueField.map_comp_residue φ`. Rewrite using `[e, ← Polynomial.hom_eval₂, hpb, map_zero]⟩`. Set `g` to `IsAlgClosed.lift (M := Ω) (R := ResidueField V) (S := ResidueField V')`.

Conclude with `⟨g.toRingHom, RingHom.ext fun a => g.commutes a⟩`.
-/
theorem exists_residue_ext {V V' : Type} [CommRing V] [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (φ : V →+* V')
    [IsLocalHom φ] (hf : φ.Finite) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ι : ResidueField V →+* Ω) :
    ∃ ι' : ResidueField V' →+* Ω, ι'.comp (ResidueField.map φ) = ι := by
  letI := (ResidueField.map φ).toAlgebra
  letI := ι.toAlgebra
  have : Algebra.IsIntegral (ResidueField V) (ResidueField V') := ⟨fun y => by
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨p, hp, hpb⟩ := hf.to_isIntegral b
    refine ⟨p.map (residue V), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (ResidueField V) (ResidueField V')).comp (residue V) = (residue V').comp φ :=
      ResidueField.map_comp_residue φ
    rw [e, ← Polynomial.hom_eval₂, hpb, map_zero]⟩
  let g := IsAlgClosed.lift (M := Ω) (R := ResidueField V) (S := ResidueField V')
  exact ⟨g.toRingHom, RingHom.ext fun a => g.commutes a⟩

/- English proof (translation)
Take `⟨T, χ, x₀, ι, hx₀, hx⟩` from `GlobalTheory.T.exists_dvr_lift_of_geometric_point E H D l Xo c Z Ω x`. Take `⟨PP, cub, sym, adj, prim, m, -⟩` from `sabPull Out.CubePf.cubePull χ Z.t`. Take `⟨PP₁, cub₁, sym₁, adj₁, prim₁, n₁, -⟩` from `sabPull Out.CubePf.cubePull x₀ Z.oF.t`. Take `⟨b, -⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ Z.m n₁`. Establish `hx₀' : x₀ ≫ Z.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ χ` using `hx₀`.

Rewrite `b` using `[hx₀']`. Take `⟨mK, -⟩` from `sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b`. Take `⟨mx, -⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ Z.m0.toSABMap n₁`. Take `⟨T', φ₁, t', m', hi, hf, ⟨P⟩⟩` from `GlobalTheory.ChartCharacters.exists_finite_ext_pelUnif Xo T _ _ mK _ mx`. Take `⟨m'', -⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m'`.

Establish `hloc : IsLocalHom φ₁` using `RingHom.IsIntegral.isLocalHom hf.to_isIntegral hi`. Take `⟨ι', hι'⟩` from `exists_residue_ext φ₁ hf Ω ι`. Establish `hx' : (spMap ι' ≫ spMap (residue T'.V)) ≫ (spMap φ₁ ≫ χ) = x`. Rewrite using `[← hx, ← hι', ← GlobalTheory.ClosedPol.spMap_comp]`. Simplify using `only [Category.assoc]`.

Use `congr 1`. Rewrite using `[← Category.assoc, ← Category.assoc]`. Use `congr 1`. Rewrite using `[GlobalTheory.ClosedPol.spMap_comp, GlobalTheory.ClosedPol.spMap_comp, ResidueField.map_comp_residue]`. Rewrite `h` using `[← hx']`.

Take `⟨φ₂, h₂⟩` from `actPull_cancel ⟨m''.cart, m''.act⟩ h`. Take `⟨G₀, _, i₀, φ₀, h₀, hP⟩` from `GlobalTheory.T.exists_reduction_polarization_part E H T' t' P`. Take `⟨φ₃, h₃⟩` from `actPull_cancel h₀ h₂`. Conclude with `GlobalTheory.T.polarization_part_base_change (𝓞 E) _ _ _ ι' G₀ i₀ G i φ₃ h₃ hP`.
-/
theorem polPart_of_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Z : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ Z.X) (G : Over (Sp Ω)) [GrpObj G]
    (i : OAct (𝓞 E) G) (φ : G.left ⟶ Z.t.G.left) (h : IsActPull i Z.t.act x φ) :
    PolPart (H.bar : 𝓞 E →+* 𝓞 E) i := by
  obtain ⟨T, χ, x₀, ι, hx₀, hx⟩ := GlobalTheory.T.exists_dvr_lift_of_geometric_point E H D l Xo c Z Ω x
  obtain ⟨PP, cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull χ Z.t
  obtain ⟨PP₁, cub₁, sym₁, adj₁, prim₁, n₁, -⟩ := sabPull Out.CubePf.cubePull x₀ Z.oF.t
  obtain ⟨b, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Z.m n₁
  have hx₀' : x₀ ≫ Z.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ χ := hx₀
  rw [hx₀'] at b
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b
  obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Z.m0.toSABMap n₁
  obtain ⟨T', φ₁, t', m', hi, hf, ⟨P⟩⟩ := GlobalTheory.ChartCharacters.exists_finite_ext_pelUnif Xo T _ _ mK _ mx
  obtain ⟨m'', -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m'
  have hloc : IsLocalHom φ₁ := RingHom.IsIntegral.isLocalHom hf.to_isIntegral hi
  obtain ⟨ι', hι'⟩ := exists_residue_ext φ₁ hf Ω ι
  have hx' : (spMap ι' ≫ spMap (residue T'.V)) ≫ (spMap φ₁ ≫ χ) = x := by
    rw [← hx, ← hι', ← GlobalTheory.ClosedPol.spMap_comp]
    simp only [Category.assoc]
    congr 1
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [GlobalTheory.ClosedPol.spMap_comp, GlobalTheory.ClosedPol.spMap_comp, ResidueField.map_comp_residue]
  rw [← hx'] at h
  obtain ⟨φ₂, h₂⟩ := actPull_cancel ⟨m''.cart, m''.act⟩ h
  obtain ⟨G₀, _, i₀, φ₀, h₀, hP⟩ := GlobalTheory.T.exists_reduction_polarization_part E H T' t' P
  obtain ⟨φ₃, h₃⟩ := actPull_cancel h₀ h₂
  exact GlobalTheory.T.polarization_part_base_change (𝓞 E) _ _ _ ι' G₀ i₀ G i φ₃ h₃ hP

/- English proof (translation)
Introduce `_ _ D O _ _ _ _ _ Ω _ _ _ x G _ i φ h`. Conclude with `polPart_of_point O.s.T.Z Ω x G i φ h`.
-/
theorem polPart_at_point : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (B : ℝ) (q : ℕ) [Fact q.Prime], q ∉ FlagAr.setB O.Y B →
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharP Ω q] (x : Sp Ω ⟶ O.s.T.Z.X) (G : Over (Sp Ω)) [GrpObj G]
    (i : OAct (𝓞 D.host.E) G) (φ : G.left ⟶ O.s.T.Z.t.G.left), IsActPull i O.s.T.Z.t.act x φ →
    PolPart (O.A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) i := by
  intro _ _ D O _ _ _ _ _ Ω _ _ _ x G _ i φ h
  exact polPart_of_point O.s.T.Z Ω x G i φ h

end GlobalTheory.PolPoint
