import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocGrLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelNormalSchemeExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelFiniteCoverNormalStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwoLat
section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l}
  (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))

/- English proof (translation)
Take `⟨V, g, e, hx, he⟩` from `GlobalTheory.LineNorm.exists_affine_isTanBasis E H Z.X Z.t X ρ x`. Use `⟨V, hx, fun τ => ?_⟩` and prove the remaining obligations. Establish `: Nonempty V.1` using `⟨⟨x, hx⟩⟩`. Use `h0 V.1` as an intermediate fact. Establish `: IsProper Z.s` using `projProper _ _ _ Z.proj`.

Establish `: FiniteDimensional ℚ c.F` using `c.fin`. Establish `: NumberField c.F` using `{}`. Establish `: IsLocallyNoetherian Z.X` using `LocallyOfFiniteType.isLocallyNoetherian Z.s`. Establish `hsep : Z.X.IsSeparated` using `⟨by rw [← Limits.terminal.comp_from Z.s]; infer_instance⟩`. Establish `: IsFractionRing Γ(X, V.1) X.functionField` using `functionField_isFractionRing_of_isAffineOpen X V.1 V.2`.

Establish `: CharZero X.functionField` using `charZero_of_injective_algebraMap (IsFractionRing.injective Γ(X, V.1) _)`. Establish `: IsIntegrallyClosed Γ(X, V.1)` using `haveI : GlobalTheory.IsNormalScheme X := ⟨fun x => (hn x).1, fun x => (hn x).2⟩ GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen V.2`. Establish `hgen : spMap (algebraMap Γ(X, V.1) X.functionField) ≫ V.2.fromSpec ≫ ρ = X.fromSpecStalk (genericPoint X) ≫ ρ`. Rewrite using `[← Category.assoc]`. Use `congr 1`.

Conclude with `V.2.fromSpecStalk_eq_fromSpecStalk (((genericPoint_spec X).mem_open_set_iff V.1.isOpen).2 ⟨x, trivial, hx⟩)`. Establish `hζ : ∃ ζ : X.functionField, IsPrimitiveRoot ζ (∏ p ∈ (∅ : Finset ℕ), p)` using `⟨1, by simpa using IsPrimitiveRoot.one⟩`. Take `⟨M, h, hP⟩` from `GlobalTheory.T.split_torus_cyclotomic_point E H Z.X Z.t hsep ∅ (fun p hp => absurd hp (Finset.notMem_empty p)) Γ(X, V.1) X.functionField (V.2.fromSpec ≫ ρ) hζ (hgen ▸ hs) g e he`. Take `⟨D, P, hD, hPr, hrk⟩` from `GlobalTheory.T.moduli_point_tangent_frame_complex E H Dw l Xo c Z _ _ τ g e he`. Establish `hP' : LatPres Z.t (R` using `Γ(X, V.1)) (V.2.fromSpec ≫ ρ) (ArIn.ind ∅) (scOf H τ (ArIn.ind ∅)) e h := by`.

Establish `e0 : scOf H τ (ArIn.ind ∅) = fun _ => 0` using `funext fun p => by simp [scOf, ArIn.ind]`. Rewrite using `[e0]`. Conclude with `hP`. Take `⟨n, m, A, hn0, hA, hsp⟩` from `GlobalTheory.T.projective_module_rank_generic_spread _ g M (Dw.mult τ) D P h hD hPr.1 hrk hP'.1`. Use `⟨n, m, A, hn0, hA, fun R' _ _ _ ψ hk => ?_⟩` and prove the remaining obligations.

Take `⟨N, U, I, hN, hU⟩` from `hsp R' ψ hk`. Conclude with `GlobalTheory.T.moduli_tangent_frame_base_change E H Dw l Xo c _ _ Z _ R' ψ _ τ _ _ g M _ D N e h P U I hD hN he hPr hP' hU`.
-/
theorem exists_chart_deRham [IsGalois ℚ E] {X : Scheme.{0}} [IsIntegral X] (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X)
    (h0 : ∀ (U : X.Opens) [Nonempty U], CharZero Γ(X, U)) (ρ : X ⟶ Z.X)
    (hs : GlobalTheory.HtGen.SplitK Z.t (K := X.functionField) (X.fromSpecStalk (genericPoint X) ≫ ρ) (∏ p ∈ (∅ : Finset ℕ), p))
    (x : X) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ ∀ τ : E →+* ℂ, ∃ (n m : ℕ) (A : Fin m → Γ(X, V.1)), n ≠ 0 ∧
      (n : Γ(X, V.1)) ∈ (Ideal.span (Set.range A)).radical ∧
      ∀ (R' : Type) [CommRing R'] [IsDomain R'] [CharZero R'] (ψ : Γ(X, V.1) →+* R'), (∃ k, ∀ k', ψ (A k) ∣ ψ (A k')) →
        RingBasis Z (spMap ψ ≫ V.2.fromSpec ≫ ρ) τ (Dw.mult τ) (ArIn.ind ∅) (scOf H τ (ArIn.ind ∅)) := by
  obtain ⟨V, g, e, hx, he⟩ := GlobalTheory.LineNorm.exists_affine_isTanBasis E H Z.X Z.t X ρ x
  refine ⟨V, hx, fun τ => ?_⟩
  have : Nonempty V.1 := ⟨⟨x, hx⟩⟩
  have := h0 V.1
  have : IsProper Z.s := projProper _ _ _ Z.proj
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := {}
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  have hsep : Z.X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from Z.s]; infer_instance⟩
  have : IsFractionRing Γ(X, V.1) X.functionField := functionField_isFractionRing_of_isAffineOpen X V.1 V.2
  have : CharZero X.functionField := charZero_of_injective_algebraMap (IsFractionRing.injective Γ(X, V.1) _)
  have : IsIntegrallyClosed Γ(X, V.1) :=
    haveI : GlobalTheory.IsNormalScheme X := ⟨fun x => (hn x).1, fun x => (hn x).2⟩
    GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen V.2
  have hgen : spMap (algebraMap Γ(X, V.1) X.functionField) ≫ V.2.fromSpec ≫ ρ =
      X.fromSpecStalk (genericPoint X) ≫ ρ := by
    rw [← Category.assoc]
    congr 1
    exact V.2.fromSpecStalk_eq_fromSpecStalk (((genericPoint_spec X).mem_open_set_iff V.1.isOpen).2 ⟨x, trivial, hx⟩)
  have hζ : ∃ ζ : X.functionField, IsPrimitiveRoot ζ (∏ p ∈ (∅ : Finset ℕ), p) :=
    ⟨1, by simpa using IsPrimitiveRoot.one⟩
  obtain ⟨M, h, hP⟩ := GlobalTheory.T.split_torus_cyclotomic_point E H Z.X Z.t hsep ∅ (fun p hp => absurd hp (Finset.notMem_empty p))
    Γ(X, V.1) X.functionField (V.2.fromSpec ≫ ρ) hζ (hgen ▸ hs) g e he
  obtain ⟨D, P, hD, hPr, hrk⟩ := GlobalTheory.T.moduli_point_tangent_frame_complex E H Dw l Xo c Z _ _ τ g e he
  have hP' : LatPres Z.t (R := Γ(X, V.1)) (V.2.fromSpec ≫ ρ) (ArIn.ind ∅) (scOf H τ (ArIn.ind ∅)) e h := by
    have e0 : scOf H τ (ArIn.ind ∅) = fun _ => 0 := funext fun p => by simp [scOf, ArIn.ind]
    rw [e0]
    exact hP
  obtain ⟨n, m, A, hn0, hA, hsp⟩ := GlobalTheory.T.projective_module_rank_generic_spread _ g M (Dw.mult τ) D P h hD hPr.1 hrk hP'.1
  refine ⟨n, m, A, hn0, hA, fun R' _ _ _ ψ hk => ?_⟩
  obtain ⟨N, U, I, hN, hU⟩ := hsp R' ψ hk
  exact GlobalTheory.T.moduli_tangent_frame_base_change E H Dw l Xo c _ _ Z _ R' ψ _ τ _ _ g M _ D N e h P U I hD hN he hPr hP' hU

end

/- English proof (translation)
Introduce `E _ _ _ _ H Dw l Xo c Z F _ _ e V _ j hj d hdim`. Take `⟨X₀, W₀, q₀, j₀, π₀, ρ₀, h₀⟩` from `GlobalTheory.T.arithmetic_model_closed_subvariety F c.F e Z.X Z.s Z.proj V j hj d hdim`. Use `h₀.1.isIntegral` as an intermediate fact. Establish `: IsProper Z.s` using `projProper _ _ _ Z.proj`. Establish `: FiniteDimensional ℚ c.F` using `c.fin`.

Establish `: NumberField c.F` using `{}`. Establish `: IsLocallyNoetherian Z.X` using `LocallyOfFiniteType.isLocallyNoetherian Z.s`. Establish `: CharZero X₀.functionField`. Use `charZero_sec h₀.1 ⊤` as an intermediate fact. Conclude with `charZero_of_injective_ringHom (f := (X₀.germToFunctionField ⊤).hom) (X₀.germToFunctionField_injective ⊤)`.

Set `x₀ : Sp X₀.functionField ⟶ Z.X` to `X₀.fromSpecStalk (genericPoint X₀) ≫ ρ₀`. Take `⟨K, i1, i2, i3, hfin, hinj, -, -, hs⟩` from `GlobalTheory.T.exists_finite_extension_splitting_torsion E H Z.X Z.t X₀.functionField x₀ (∏ p ∈ (∅ : Finset ℕ), p) (by simp)`. Establish `hK : IsField K`. Establish `: Algebra.IsIntegral X₀.functionField K` using `Algebra.IsIntegral.of_finite _ _`. Conclude with `(Algebra.IsIntegral.isField_iff_isField hinj).1 (Field.toIsField _)`.

Use `letI : Field K := hK.toField`. Take `⟨X₁, W₁, _, ν₁, j₁, π₁, κ, h₁, hn₁, hκ⟩` from `GlobalTheory.T.arithmetic_model_finite_extension F _ _ _ _ d _ X₀ W₀ q₀ j₀ π₀ ρ₀ h₀ K hfin`. Establish `hsK : GlobalTheory.HtGen.SplitK Z.t (K` using `X₁.functionField) (X₁.fromSpecStalk (genericPoint X₁) ≫ ν₁ ≫ ρ₀) (∏ p ∈ (∅ : Finset ℕ), p) := GlobalTheory.HtGen.SplitCover.splitK_of_splitTors Z.t _ κ _ (by rw [reassoc_of% hκ]) hs`. Establish `hsK1 : GlobalTheory.HtGen.SplitK Z.t (K` using `X₁.functionField) (X₁.fromSpecStalk (genericPoint X₁) ≫ ν₁ ≫ ρ₀) 1 := by`. Simplify using `using hsK`.

Establish `h0₁ : ∀ (U : X₁.Opens) [Nonempty U], CharZero Γ(X₁, U)` using `fun U _ => charZero_sec h₁.1 U`. Establish `hch : ∀ (b : Bool) (τ : E →+* ℂ) (x : X₁), ∃ V : X₁.affineOpens, x ∈ V.1 ∧ ∃ (n m : ℕ) (A : Fin m → Γ(X₁, V.1)), n ≠ 0 ∧ (n : Γ(X₁, V.1)) ∈ (Ideal.span (Set.range A)).radical ∧ ∀ (R' : Type) [CommRing R'] [IsDomain R'] [CharZero R'] (ψ : Γ(X₁, V.1) →+* R'), (∃ k, ∀ k', ψ (A k) ∣ …`. Introduce `b τ x`. Consider the cases of `b with`. Consider the case `true`.

Take `⟨V, hV, hc⟩` from `exists_chart_deRham Z hn₁ h0₁ (ν₁ ≫ ρ₀) hsK x`. Conclude with `⟨V, hV, hc τ⟩`. Consider the case `false => exact GlobalTheory.T.toroidal_model_normal_scheme_extension Z hn₁ h0₁ (ν₁ ≫ ρ₀) hsK1 x τ`. Use `choose V hV n m A hn hA hR using hch`. Establish `: IsProper (ν₁ ≫ q₀)` using `projProper _ _ _ h₁.1.isProjOver`.

Establish `: CompactSpace X₁` using `QuasiCompact.compactSpace_of_compactSpace (ν₁ ≫ q₀)`. Establish `hcov : ∀ bτ : Bool × (E →+* ℂ), ∃ t : Finset X₁, ∀ y : X₁, ∃ x ∈ t, y ∈ (V bτ.1 bτ.2 x).1`. Introduce `bτ`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun x : X₁ => ((V bτ.1 bτ.2 x).1 : Set X₁)) (fun x => (V bτ.1 bτ.2 x).1.isOpen) fun x _ => Set.mem_iUnion.2 ⟨x, hV bτ.1 bτ.2 x⟩`. Use `⟨t, fun y => ?_⟩` and prove the remaining obligations.

Take `⟨x, hx, hy⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ y))`. Conclude with `⟨x, hx, hy⟩`. Use `choose t ht using hcov`. Set `ε` to `(Fintype.equivFin (Σ bτ : Bool × (E →+* ℂ), t bτ)).symm`. Take `⟨X₂, W₂, bl, j₂, π₂, h₂, hb⟩` from `GlobalTheory.T.arithmetic_model_affine_cover_radical F _ _ _ _ d _ X₁ W₁ _ j₁ π₁ _ h₁ _ (fun k => (V (ε k).1.1 (ε k).1.2 (ε k).2).1) (fun k => m (ε k).1.1 (ε k).1.2 (ε k).2) (fun k => A (ε k).1.1 (ε k).1.2 (ε k).2) (fun k => n (ε k).1.1 (ε k).1.2 (ε k).2) (fun k => (V _ _ _).2) ( …`.

Use `h₂.1.isIntegral` as an intermediate fact. Take `⟨X₃, W₃, _, ν₃, j₃, π₃, -, h₃, hn₃, -⟩` from `GlobalTheory.T.arithmetic_model_finite_extension F _ _ _ _ d _ X₂ W₂ _ j₂ π₂ _ h₂ X₂.functionField inferInstance`. Establish `key : ∀ (b : Bool) (τ : E →+* ℂ) (w : X₃), ∃ (U : X₃.Opens) (hUa : IsAffineOpen U), w ∈ U ∧ cond b (RingBasis Z (R` using `Γ(X₃, U)) (hUa.fromSpec ≫ ν₃ ≫ bl ≫ ν₁ ≫ ρ₀) τ (Dw.mult τ) (ArIn.ind ∅) (scOf H τ (ArIn.ind ∅))) (GlobalTheory.TwoLat.GrBasis Z (R := Γ(X₃, U)) (hUa.fromSpec ≫ ν₃ ≫ bl ≫ ν₁ ≫ ρ₀) τ (Dw.mult τ)) := by`. Introduce `b τ w`. Take `⟨x, hx, hw⟩` from `ht (b, τ) ((ν₃ ≫ bl) w)`.

Take `⟨k, hk⟩` from `ε.surjective ⟨(b, τ), ⟨x, hx⟩⟩`. Establish `hw' : (ν₃ ≫ bl) w ∈ (V (ε k).1.1 (ε k).1.2 (ε k).2).1` using `by rw [hk]; exact hw`. Take `⟨U, hU, hwU, hUa, hdv⟩` from `hb X₃ ν₃ w k hw'`. Establish `: Nonempty U` using `⟨⟨w, hwU⟩⟩`. Use `charZero_sec h₃.1 U` as an intermediate fact.

Establish `hRB` using `hR (ε k).1.1 (ε k).1.2 (ε k).2 Γ(X₃, U) _ hdv`. Establish `e₁ : spMap ((ν₃ ≫ bl).appLE (V (ε k).1.1 (ε k).1.2 (ε k).2).1 U hU).hom ≫ (V (ε k).1.1 (ε k).1.2 (ε k).2).2.fromSpec ≫ ν₁ ≫ ρ₀ = hUa.fromSpec ≫ ν₃ ≫ bl ≫ ν₁ ≫ ρ₀`. Use `IsAffineOpen.SpecMap_appLE_fromSpec (ν₃ ≫ bl) (V (ε k).1.1 (ε k).1.2 (ε k).2).2 hUa hU` as an intermediate fact. Rewrite using `[← Category.assoc]`. Use `(congrArg (· ≫ ν₁ ≫ ρ₀) this).trans ?_` and prove the remaining obligations.

Simplify using `only [Category.assoc]`. Rewrite `hRB` using `[e₁]`. Establish `hb1 : (ε k).1.1 = b` using `by rw [hk]`. Establish `hτ1 : (ε k).1.2 = τ` using `by rw [hk]`. Rewrite `hRB` using `[hb1, hτ1]`.

Conclude with `⟨U, hUa, hwU, hRB⟩`. Use `⟨X₃, W₃, _, j₃, π₃, _, h₃, hn₃, fun τ w => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨U, hUa, hwU, hRB⟩` from `key true τ w`. Take `⟨u, hu⟩` from `GlobalTheory.T.arithmetic_model_flag_compactification E H Dw l Xo c _ _ Z F e X₃ W₃ j₃ π₃ _ h₃.2.2.2.2 U hUa τ _ _ hRB`. Conclude with `⟨U, u, hwU, hUa, hu⟩`.

Take `⟨U, hUa, hwU, hRB⟩` from `key false τ w`. Take `⟨u, hu⟩` from `GlobalTheory.T.toroidal_model_finite_cover_normal Z e j₃ π₃ _ h₃.2.2.2.2 U hUa τ _ hRB`. Conclude with `⟨U, u, hwU, hUa, hu⟩`.
-/
theorem exists_base_deRham : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l}
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) {F : Type} [Field F] [NumberField F]
    (e : F ≃+* c.F) {V : Scheme.{0}} [IsIntegral V] (j : V ⟶ gen Z), IsClosedImmersion j → ∀ {d : ℕ},
    topologicalKrullDim V = d →
    ∃ (X W : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ gen Z) (ρ : X ⟶ Z.X),
      IsPre (genStr Z ≫ spMap e.toRingHom) (Set.range j) d (genι Z) q jB πB ρ ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X ∧ ∀ (τ : E →+* ℂ) (x : X),
        (∃ (U : X.Opens) (u : LocAssign Z (Dw.mult τ) jB U), x ∈ U ∧ IsAffineOpen U ∧
          IsLocFrame Z e jB πB _ τ U u ∧ IsLocLat Z e jB πB _ τ (ArIn.ind ∅) U u) ∧
        ∃ (U : X.Opens) (u : LocAssign Z (Dw.mult τ) jB U), x ∈ U ∧ IsAffineOpen U ∧
          IsLocFrame Z e jB πB _ τ U u ∧ GlobalTheory.TwoLat.IsLocGrLat Z e jB πB _ τ U u := by
  intro E _ _ _ _ H Dw l Xo c Z F _ _ e V _ j hj d hdim
  classical
  obtain ⟨X₀, W₀, q₀, j₀, π₀, ρ₀, h₀⟩ := GlobalTheory.T.arithmetic_model_closed_subvariety F c.F e Z.X Z.s Z.proj V j hj d hdim
  have := h₀.1.isIntegral
  have : IsProper Z.s := projProper _ _ _ Z.proj
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := {}
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  have : CharZero X₀.functionField := by
    have := charZero_sec h₀.1 ⊤
    exact charZero_of_injective_ringHom (f := (X₀.germToFunctionField ⊤).hom) (X₀.germToFunctionField_injective ⊤)
  let x₀ : Sp X₀.functionField ⟶ Z.X := X₀.fromSpecStalk (genericPoint X₀) ≫ ρ₀
  obtain ⟨K, i1, i2, i3, hfin, hinj, -, -, hs⟩ :=
    GlobalTheory.T.exists_finite_extension_splitting_torsion E H Z.X Z.t X₀.functionField x₀ (∏ p ∈ (∅ : Finset ℕ), p) (by simp)
  have hK : IsField K := by
    have : Algebra.IsIntegral X₀.functionField K := Algebra.IsIntegral.of_finite _ _
    exact (Algebra.IsIntegral.isField_iff_isField hinj).1 (Field.toIsField _)
  letI : Field K := hK.toField
  obtain ⟨X₁, W₁, _, ν₁, j₁, π₁, κ, h₁, hn₁, hκ⟩ := GlobalTheory.T.arithmetic_model_finite_extension F _ _ _ _ d _ X₀ W₀ q₀ j₀ π₀ ρ₀ h₀ K hfin
  have hsK : GlobalTheory.HtGen.SplitK Z.t (K := X₁.functionField) (X₁.fromSpecStalk (genericPoint X₁) ≫ ν₁ ≫ ρ₀)
      (∏ p ∈ (∅ : Finset ℕ), p) :=
    GlobalTheory.HtGen.SplitCover.splitK_of_splitTors Z.t _ κ _ (by rw [reassoc_of% hκ]) hs
  have hsK1 : GlobalTheory.HtGen.SplitK Z.t (K := X₁.functionField) (X₁.fromSpecStalk (genericPoint X₁) ≫ ν₁ ≫ ρ₀) 1 := by
    simpa using hsK
  have h0₁ : ∀ (U : X₁.Opens) [Nonempty U], CharZero Γ(X₁, U) := fun U _ => charZero_sec h₁.1 U
  have hch : ∀ (b : Bool) (τ : E →+* ℂ) (x : X₁), ∃ V : X₁.affineOpens, x ∈ V.1 ∧
      ∃ (n m : ℕ) (A : Fin m → Γ(X₁, V.1)), n ≠ 0 ∧ (n : Γ(X₁, V.1)) ∈ (Ideal.span (Set.range A)).radical ∧
        ∀ (R' : Type) [CommRing R'] [IsDomain R'] [CharZero R'] (ψ : Γ(X₁, V.1) →+* R'),
          (∃ k, ∀ k', ψ (A k) ∣ ψ (A k')) →
          cond b (RingBasis Z (spMap ψ ≫ V.2.fromSpec ≫ ν₁ ≫ ρ₀) τ (Dw.mult τ) (ArIn.ind ∅) (scOf H τ (ArIn.ind ∅)))
            (GlobalTheory.TwoLat.GrBasis Z (spMap ψ ≫ V.2.fromSpec ≫ ν₁ ≫ ρ₀) τ (Dw.mult τ)) := by
    intro b τ x
    cases b with
    | true =>
      obtain ⟨V, hV, hc⟩ := exists_chart_deRham Z hn₁ h0₁ (ν₁ ≫ ρ₀) hsK x
      exact ⟨V, hV, hc τ⟩
    | false => exact GlobalTheory.T.toroidal_model_normal_scheme_extension Z hn₁ h0₁ (ν₁ ≫ ρ₀) hsK1 x τ
  choose V hV n m A hn hA hR using hch
  have : IsProper (ν₁ ≫ q₀) := projProper _ _ _ h₁.1.isProjOver
  have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace (ν₁ ≫ q₀)
  have hcov : ∀ bτ : Bool × (E →+* ℂ), ∃ t : Finset X₁, ∀ y : X₁, ∃ x ∈ t, y ∈ (V bτ.1 bτ.2 x).1 := by
    intro bτ
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X₁ => ((V bτ.1 bτ.2 x).1 : Set X₁))
      (fun x => (V bτ.1 bτ.2 x).1.isOpen) fun x _ => Set.mem_iUnion.2 ⟨x, hV bτ.1 bτ.2 x⟩
    refine ⟨t, fun y => ?_⟩
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨x, hx, hy⟩
  choose t ht using hcov
  let ε := (Fintype.equivFin (Σ bτ : Bool × (E →+* ℂ), t bτ)).symm
  obtain ⟨X₂, W₂, bl, j₂, π₂, h₂, hb⟩ := GlobalTheory.T.arithmetic_model_affine_cover_radical F _ _ _ _ d _ X₁ W₁ _ j₁ π₁ _ h₁ _
    (fun k => (V (ε k).1.1 (ε k).1.2 (ε k).2).1) (fun k => m (ε k).1.1 (ε k).1.2 (ε k).2)
    (fun k => A (ε k).1.1 (ε k).1.2 (ε k).2) (fun k => n (ε k).1.1 (ε k).1.2 (ε k).2) (fun k => (V _ _ _).2)
    (fun k => hn _ _ _) (fun k => hA _ _ _)
  have := h₂.1.isIntegral
  obtain ⟨X₃, W₃, _, ν₃, j₃, π₃, -, h₃, hn₃, -⟩ :=
    GlobalTheory.T.arithmetic_model_finite_extension F _ _ _ _ d _ X₂ W₂ _ j₂ π₂ _ h₂ X₂.functionField inferInstance
  have key : ∀ (b : Bool) (τ : E →+* ℂ) (w : X₃), ∃ (U : X₃.Opens) (hUa : IsAffineOpen U), w ∈ U ∧
      cond b (RingBasis Z (R := Γ(X₃, U)) (hUa.fromSpec ≫ ν₃ ≫ bl ≫ ν₁ ≫ ρ₀) τ (Dw.mult τ) (ArIn.ind ∅)
          (scOf H τ (ArIn.ind ∅)))
        (GlobalTheory.TwoLat.GrBasis Z (R := Γ(X₃, U)) (hUa.fromSpec ≫ ν₃ ≫ bl ≫ ν₁ ≫ ρ₀) τ (Dw.mult τ)) := by
    intro b τ w
    obtain ⟨x, hx, hw⟩ := ht (b, τ) ((ν₃ ≫ bl) w)
    obtain ⟨k, hk⟩ := ε.surjective ⟨(b, τ), ⟨x, hx⟩⟩
    have hw' : (ν₃ ≫ bl) w ∈ (V (ε k).1.1 (ε k).1.2 (ε k).2).1 := by rw [hk]; exact hw
    obtain ⟨U, hU, hwU, hUa, hdv⟩ := hb X₃ ν₃ w k hw'
    have : Nonempty U := ⟨⟨w, hwU⟩⟩
    have := charZero_sec h₃.1 U
    have hRB := hR (ε k).1.1 (ε k).1.2 (ε k).2 Γ(X₃, U) _ hdv
    have e₁ : spMap ((ν₃ ≫ bl).appLE (V (ε k).1.1 (ε k).1.2 (ε k).2).1 U hU).hom ≫
        (V (ε k).1.1 (ε k).1.2 (ε k).2).2.fromSpec ≫ ν₁ ≫ ρ₀ = hUa.fromSpec ≫ ν₃ ≫ bl ≫ ν₁ ≫ ρ₀ := by
      have := IsAffineOpen.SpecMap_appLE_fromSpec (ν₃ ≫ bl) (V (ε k).1.1 (ε k).1.2 (ε k).2).2 hUa hU
      rw [← Category.assoc]
      refine (congrArg (· ≫ ν₁ ≫ ρ₀) this).trans ?_
      simp only [Category.assoc]
    rw [e₁] at hRB
    have hb1 : (ε k).1.1 = b := by rw [hk]
    have hτ1 : (ε k).1.2 = τ := by rw [hk]
    rw [hb1, hτ1] at hRB
    exact ⟨U, hUa, hwU, hRB⟩
  refine ⟨X₃, W₃, _, j₃, π₃, _, h₃, hn₃, fun τ w => ⟨?_, ?_⟩⟩
  · obtain ⟨U, hUa, hwU, hRB⟩ := key true τ w
    obtain ⟨u, hu⟩ := GlobalTheory.T.arithmetic_model_flag_compactification E H Dw l Xo c _ _ Z F e X₃ W₃ j₃ π₃ _ h₃.2.2.2.2 U hUa τ _ _ hRB
    exact ⟨U, u, hwU, hUa, hu⟩
  · obtain ⟨U, hUa, hwU, hRB⟩ := key false τ w
    obtain ⟨u, hu⟩ := GlobalTheory.T.toroidal_model_finite_cover_normal Z e j₃ π₃ _ h₃.2.2.2.2 U hUa τ _ hRB
    exact ⟨U, u, hwU, hUa, hu⟩

end GlobalTheory.TwoLat

end
