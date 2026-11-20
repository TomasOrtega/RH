import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightWeightRootChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqnRatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightOfInducedBundle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetsOfParOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CategoryTheory AlgebraicGeometry IsDedekindDomain GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Classical GlobalTheory.HtAdd

namespace GlobalTheory.HtAdd.ProdFormulaPts

open Function

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `h` using `(FinitePlace.hasFiniteMulSupport hb)`. Establish `h' : (mulSupport fun w : FinitePlace F => w b).Finite` using `h`. Establish `e : (mulSupport fun v : HeightOneSpectrum (𝓞 F) => HeightOneSpectrum.adicAbv F v b) = FinitePlace.equivHeightOneSpectrum '' (mulSupport fun w : FinitePlace F => w b)`. Use extensionality with `v`. Rewrite using `[Equiv.image_eq_preimage_symm]`.

Simplify using `only [mem_mulSupport, Set.mem_preimage, FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]`. Rewrite using `[e]`. Conclude with `h'.image _`.
-/
theorem finite_mulSupport_adicAbv {b : F} (hb : b ≠ 0) :
    (mulSupport fun v : HeightOneSpectrum (𝓞 F) => HeightOneSpectrum.adicAbv F v b).Finite := by
  have h := (FinitePlace.hasFiniteMulSupport hb)
  have h' : (mulSupport fun w : FinitePlace F => w b).Finite := h
  have e : (mulSupport fun v : HeightOneSpectrum (𝓞 F) => HeightOneSpectrum.adicAbv F v b) =
      FinitePlace.equivHeightOneSpectrum '' (mulSupport fun w : FinitePlace F => w b) := by
    ext v
    rw [Equiv.image_eq_preimage_symm]
    simp only [mem_mulSupport, Set.mem_preimage, FinitePlace.equivHeightOneSpectrum_symm_apply,
      FinitePlace.norm_embedding]
  rw [e]
  exact h'.image _

/- English proof (translation)
Use `(finite_mulSupport_adicAbv hb).subset fun v hv => ?_` and prove the remaining obligations. Rewrite `hv` using `[mem_support]`. Rewrite using `[mem_mulSupport]`. Introduce `h1`. Conclude with `hv (by rw [h1, Real.log_one])`.
-/
theorem finite_support_log_adicAbv {b : F} (hb : b ≠ 0) :
    (support fun v : HeightOneSpectrum (𝓞 F) => Real.log (HeightOneSpectrum.adicAbv F v b)).Finite := by
  refine (finite_mulSupport_adicAbv hb).subset fun v hv => ?_
  rw [mem_support] at hv
  rw [mem_mulSupport]
  intro h1
  exact hv (by rw [h1, Real.log_one])

/- English proof (translation)
Establish `hs` using `finite_mulSupport_adicAbv hb`. Establish `hl` using `finite_support_log_adicAbv hb`. Establish `hp : ∏ᶠ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicAbv F v b = ((|Algebra.norm ℚ b|⁻¹ : ℚ) : ℝ)`. Rewrite using `[← FinitePlace.prod_eq_inv_abs_norm hb, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]`. Simplify using `only [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]`.

Establish `e1 : ∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.log (HeightOneSpectrum.adicAbv F v b) = ∑ v ∈ hs.toFinset, Real.log (HeightOneSpectrum.adicAbv F v b)`. Use `finsum_eq_sum_of_support_subset _ ?_` and prove the remaining obligations. Introduce `v hv`. Rewrite using `[Set.Finite.coe_toFinset]`. Rewrite `hv` using `[mem_support]`.

Rewrite using `[mem_mulSupport]`. Introduce `h1`. Conclude with `hv (by rw [h1, Real.log_one])`. Establish `e2 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicAbv F v b = ∏ v ∈ hs.toFinset, HeightOneSpectrum.adicAbv F v b` using `finprod_eq_prod_of_mulSupport_subset _ (by rw [Set.Finite.coe_toFinset])`. Rewrite using `[e1, ← Real.log_prod (fun v _ => (AbsoluteValue.pos _ hb).ne'), ← e2, hp]`.

Use `push_cast`. Rewrite using `[Real.log_inv]`.
-/
theorem finsum_log_adicAbv {b : F} (hb : b ≠ 0) :
    ∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.log (HeightOneSpectrum.adicAbv F v b) = -Real.log |Algebra.norm ℚ b| := by
  have hs := finite_mulSupport_adicAbv hb
  have hl := finite_support_log_adicAbv hb
  have hp : ∏ᶠ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicAbv F v b =
      ((|Algebra.norm ℚ b|⁻¹ : ℚ) : ℝ) := by
    rw [← FinitePlace.prod_eq_inv_abs_norm hb, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    simp only [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  have e1 : ∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.log (HeightOneSpectrum.adicAbv F v b) =
      ∑ v ∈ hs.toFinset, Real.log (HeightOneSpectrum.adicAbv F v b) := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro v hv
    rw [Set.Finite.coe_toFinset]
    rw [mem_support] at hv
    rw [mem_mulSupport]
    intro h1
    exact hv (by rw [h1, Real.log_one])
  have e2 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicAbv F v b =
      ∏ v ∈ hs.toFinset, HeightOneSpectrum.adicAbv F v b :=
    finprod_eq_prod_of_mulSupport_subset _ (by rw [Set.Finite.coe_toFinset])
  rw [e1, ← Real.log_prod (fun v _ => (AbsoluteValue.pos _ hb).ne'), ← e2, hp]
  push_cast
  rw [Real.log_inv]

/- English proof (translation)
Distinguish the cases in `hb : b = 0`. Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[← Real.log_prod (fun σ _ => by simpa using hb)]`. Use `congr 1`.

Establish `h` using `Algebra.norm_eq_prod_embeddings ℚ ℂ b`. Establish `h2 : ∏ σ : F →+* ℂ, σ b = ∏ τ : F →ₐ[ℚ] ℂ, τ b` using `Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun σ => rfl)`. Rewrite using `[← norm_prod, h2, ← h]`. Simplify using the standard rewrite rules.
-/
theorem sum_log_norm_embeddings (b : F) :
    ∑ σ : F →+* ℂ, Real.log ‖σ b‖ = Real.log |(Algebra.norm ℚ b : ℝ)| := by
  by_cases hb : b = 0
  · subst hb
    simp
  rw [← Real.log_prod (fun σ _ => by simpa using hb)]
  congr 1
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ b
  have h2 : ∏ σ : F →+* ℂ, σ b = ∏ τ : F →ₐ[ℚ] ℂ, τ b :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun σ => rfl)
  rw [← norm_prod, h2, ← h]
  simp

/- English proof (translation)
Rewrite using `[sum_log_norm_embeddings, finsum_log_adicAbv hb]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem product_formula {b : F} (hb : b ≠ 0) :
    (∑ σ : F →+* ℂ, Real.log ‖σ b‖) +
      ∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.log (HeightOneSpectrum.adicAbv F v b) = 0 := by
  rw [sum_log_norm_embeddings, finsum_log_adicAbv hb]
  push_cast
  ring

end GlobalTheory.HtAdd.ProdFormulaPts

namespace GlobalTheory.HtAdd.ProdFormulaPts

section Geo

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]

/- English proof (translation)
Substitute `h` using the available equality. Establish `e : ψ = Scheme.descResidueField (Scheme.stalkClosedPointTo y)`. Apply `Spec.map_injective` to reduce the goal to its premises. Apply `(cancel_mono (X.fromSpecResidueField (below y))).1` to reduce the goal to its premises. Rewrite using `[hψ]`.

Conclude with `(Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X y).symm`. Substitute `e` using the available equality. Rewrite using `[Base.valAt_stalk]`. Conclude with `(congrArg (fun q => q.hom a) (Scheme.residue_descResidueField (Scheme.stalkClosedPointTo y))).symm`.
-/
theorem valAt_of_factor (y : Sp K ⟶ X) (x : X) (h : below y = x) (ψ : X.residueField x ⟶ CommRingCat.of K)
    (hψ : Spec.map ψ ≫ X.fromSpecResidueField x = y) (a : X.presheaf.stalk x) :
    GlobalTheory.TrueGeo.valAt y (algebraMap (X.presheaf.stalk x) X.functionField a) = ψ.hom ((X.residue x).hom a) := by
  subst h
  have e : ψ = Scheme.descResidueField (Scheme.stalkClosedPointTo y) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecResidueField (below y))).1
    rw [hψ]
    exact (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X y).symm
  subst e
  rw [Base.valAt_stalk]
  exact (congrArg (fun q => q.hom a) (Scheme.residue_descResidueField (Scheme.stalkClosedPointTo y))).symm

variable {F : Type} [Field F] (s : X ⟶ Sp F) (x : X) (φ₀ : CommRingCat.of F ⟶ X.residueField x)
  (hφ₀ : Spec.map φ₀ = X.fromSpecResidueField x ≫ s) (φ : F →+* K)

noncomputable def toPt (ψ : {ψ : X.residueField x →+* K // ψ.comp φ₀.hom = φ}) :
    {y : {y : Sp K ⟶ X // y ≫ s = spMap φ} // below y.1 = x} :=
  ⟨⟨Spec.map (CommRingCat.ofHom ψ.1) ≫ X.fromSpecResidueField x, by
      rw [Category.assoc, ← hφ₀, ← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext ψ.2)⟩, ExtConj.below_comp x _⟩

/- English proof (translation)
Use `⟨fun a b h => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Spec.map (CommRingCat.ofHom a.1) ≫ X.fromSpecResidueField x = Spec.map (CommRingCat.ofHom b.1) ≫ X.fromSpecResidueField x` using `congrArg (fun t => t.1.1) h`. Conclude with `Subtype.ext (congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h1)))`. Introduce and unpack `⟨⟨y, hy⟩, hyx⟩`. Take `⟨ψ, h⟩` from `ExtConj.factor y x hyx`.

Establish `h2 : Spec.map (φ₀ ≫ ψ) = Spec.map (CommRingCat.ofHom φ)`. Rewrite using `[Spec.map_comp, hφ₀, ← Category.assoc, h]`. Conclude with `hy`. Establish `h3` using `Spec.map_injective h2`. Conclude with `⟨⟨ψ.hom, congrArg CommRingCat.Hom.hom h3⟩, Subtype.ext (Subtype.ext h)⟩`.
-/
theorem toPt_bijective : Function.Bijective (toPt s x φ₀ hφ₀ φ) := by
  refine ⟨fun a b h => ?_, ?_⟩
  · have h1 : Spec.map (CommRingCat.ofHom a.1) ≫ X.fromSpecResidueField x =
        Spec.map (CommRingCat.ofHom b.1) ≫ X.fromSpecResidueField x := congrArg (fun t => t.1.1) h
    exact Subtype.ext (congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h1)))
  · rintro ⟨⟨y, hy⟩, hyx⟩
    obtain ⟨ψ, h⟩ := ExtConj.factor y x hyx
    have h2 : Spec.map (φ₀ ≫ ψ) = Spec.map (CommRingCat.ofHom φ) := by
      rw [Spec.map_comp, hφ₀, ← Category.assoc, h]
      exact hy
    have h3 := Spec.map_injective h2
    exact ⟨⟨ψ.hom, congrArg CommRingCat.Hom.hom h3⟩, Subtype.ext (Subtype.ext h)⟩

include hφ₀ in

/- English proof (translation)
Rewrite using `[← finsum_subtype_eq_finsum_cond (fun y : {y : Sp K ⟶ X // y ≫ s = spMap φ} => below y.1 = x) (f := fun y => f (GlobalTheory.TrueGeo.valAt y.1 (algebraMap (X.presheaf.stalk x) X.functionField a)))]`. Rewrite using `[← finsum_comp_equiv (Equiv.ofBijective _ (toPt_bijective s x φ₀ hφ₀ φ))]`. Use `finsum_congr fun ψ => ?_` and prove the remaining obligations. Conclude with `congrArg f (valAt_of_factor _ x (ExtConj.below_comp x _) _ rfl a)`.
-/
theorem finsum_pts (f : K → ℝ) (a : X.presheaf.stalk x) :
    ∑ᶠ (y : {y : Sp K ⟶ X // y ≫ s = spMap φ}) (_ : below y.1 = x),
        f (GlobalTheory.TrueGeo.valAt y.1 (algebraMap (X.presheaf.stalk x) X.functionField a)) =
      ∑ᶠ ψ : {ψ : X.residueField x →+* K // ψ.comp φ₀.hom = φ}, f (ψ.1 ((X.residue x).hom a)) := by
  rw [← finsum_subtype_eq_finsum_cond (fun y : {y : Sp K ⟶ X // y ≫ s = spMap φ} => below y.1 = x)
    (f := fun y => f (GlobalTheory.TrueGeo.valAt y.1 (algebraMap (X.presheaf.stalk x) X.functionField a)))]
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (toPt_bijective s x φ₀ hφ₀ φ))]
  refine finsum_congr fun ψ => ?_
  exact congrArg f (valAt_of_factor _ x (ExtConj.below_comp x _) _ rfl a)

end Geo

section Norm

variable {F K L : Type} [Field F] [Field K] [IsAlgClosed K] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] (φ : F →+* K)

noncomputable def homsEquiv :
    letI := φ.toAlgebra
    {ψ : L →+* K // ψ.comp (algebraMap F L) = φ} ≃ (L →ₐ[F] K) :=
  letI := φ.toAlgebra
  { toFun := fun ψ => { ψ.1 with commutes' := fun c => congrArg (fun t : F →+* K => t c) ψ.2 }
    invFun := fun σ => ⟨σ.toRingHom, σ.comp_algebraMap⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/- English proof (translation)
Use `letI := φ.toAlgebra`. Set `e` to `homsEquiv (L := L) φ`. Use `haveI : Finite {ψ : L →+* K // ψ.comp (algebraMap F L) = φ} := Finite.of_equiv _ e.symm`. Use `haveI := Fintype.ofFinite {ψ : L →+* K // ψ.comp (algebraMap F L) = φ}`. Rewrite using `[finsum_eq_sum_of_fintype, ← Real.log_prod (fun ψ _ => hf _ ((map_ne_zero ψ.1).2 hr)), ← map_prod]`.

Use `congr 2`. Establish `h` using `Algebra.norm_eq_prod_embeddings F K r`. Use `Eq.trans ?_ h.symm` and prove the remaining obligations. Conclude with `Fintype.prod_equiv e _ _ (fun ψ => rfl)`.
-/
theorem finsum_log (f : K →*₀ ℝ) (hf : ∀ c, c ≠ 0 → f c ≠ 0) {r : L} (hr : r ≠ 0) :
    ∑ᶠ ψ : {ψ : L →+* K // ψ.comp (algebraMap F L) = φ}, Real.log (f (ψ.1 r)) =
      Real.log (f (φ (Algebra.norm F r))) := by
  letI := φ.toAlgebra
  let e := homsEquiv (L := L) φ
  haveI : Finite {ψ : L →+* K // ψ.comp (algebraMap F L) = φ} := Finite.of_equiv _ e.symm
  haveI := Fintype.ofFinite {ψ : L →+* K // ψ.comp (algebraMap F L) = φ}
  rw [finsum_eq_sum_of_fintype, ← Real.log_prod (fun ψ _ => hf _ ((map_ne_zero ψ.1).2 hr)), ← map_prod]
  congr 2
  have h := Algebra.norm_eq_prod_embeddings F K r
  refine Eq.trans ?_ h.symm
  exact Fintype.prod_equiv e _ _ (fun ψ => rfl)

end Norm

end GlobalTheory.HtAdd.ProdFormulaPts

open GlobalTheory.HtAdd.ProdFormulaPts in
/- English proof (translation)
Introduce `F _ _ Y x hx g hg`. Take `⟨a₀, hu, rfl⟩` from `hg`. Use `isClosed_singleton_iff_isClosedImmersion.1 hx` as an intermediate fact. Take `⟨φ₀, hφ₀⟩` from `Spec.map_surjective (Y.X.fromSpecResidueField x ≫ Y.str)`. Establish `hfin : IsFinite (Spec.map φ₀)`.

Rewrite using `[hφ₀]`. Conclude with `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance`. Use `letI : Algebra F (Y.X.residueField x) := φ₀.hom.toAlgebra`. Use `haveI : Module.Finite F (Y.X.residueField x) := (IsFinite.SpecMap_iff φ₀).1 hfin`. Establish `hr : (Y.X.residue x).hom a₀ ≠ 0` using `(hu.map (Y.X.residue x).hom).ne_zero`.

Establish `hb : Algebra.norm F ((Y.X.residue x).hom a₀) ≠ 0` using `Algebra.norm_ne_zero_iff.2 hr`. Establish `hfv : (fun v : HeightOneSpectrum (𝓞 F) => if h : Nonempty (Ext v) then ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), Real.log (h.some.w (GlobalTheory.TrueGeo.valAt y.1 (algebraMap (Y.X.presheaf.stalk x) Y.X.functionField a₀))) else 0) = fun v => Real.log (HeightOneSpectrum.adicAbv F v (A …`. Use function extensionality and compare the values at `v`. Establish `hne : Nonempty (Ext v)` using `(ExtConj.main F).1 v`. Rewrite using `[dif_pos hne]`.

Use `(finsum_pts Y.str x φ₀ hφ₀ (algebraMap F (AlgebraicClosure F)) (fun c => Real.log (hne.some.w c)) a₀).trans ?_` and prove the remaining obligations. Use `(finsum_log (algebraMap F (AlgebraicClosure F)) hne.some.w.toMonoidWithZeroHom (fun c hc => (hne.some.w.pos hc).ne') hr).trans ?_` and prove the remaining obligations. Conclude with `congrArg Real.log (hne.some.w_alg _)`. Establish `hσ : ∀ σ : F →+* ℂ, ∑ᶠ (z : Pts Y σ) (_ : under z = x), Real.log ‖ratVal (algebraMap (Y.X.presheaf.stalk x) Y.X.functionField a₀) z‖ = Real.log ‖σ (Algebra.norm F ((Y.X.residue x).hom a₀))‖`. Introduce `σ`.

Establish `e : ∑ᶠ (z : Pts Y σ) (_ : under z = x), Real.log ‖ratVal (algebraMap (Y.X.presheaf.stalk x) Y.X.functionField a₀) z‖ = ∑ᶠ (z : {z : Sp ℂ ⟶ Y.X // z ≫ Y.str = spMap σ}) (_ : below z.1 = x), Real.log ‖GlobalTheory.TrueGeo.valAt z.1 (algebraMap (Y.X.presheaf.stalk x) Y.X.functionFie …`. Use `finsum_congr fun z => finsum_congr fun hz => ?_` and prove the remaining obligations. Establish `hreg : RegAt (under z) (algebraMap (Y.X.presheaf.stalk x) Y.X.functionField a₀)`. Rewrite using `[hz]`. Conclude with `⟨a₀, rfl⟩`.

Rewrite using `[Res.ratVal_eq_valAt z hreg]`. Use `e.trans ((finsum_pts Y.str x φ₀ hφ₀ σ (fun c => Real.log ‖c‖) a₀).trans ?_)` and prove the remaining obligations. Conclude with `finsum_log σ (normHom : ℂ →*₀ ℝ) (fun c hc => norm_ne_zero_iff.2 hc) hr`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfv]`.

Conclude with `finite_support_log_adicAbv hb`. Rewrite using `[hfv, Finset.sum_congr rfl (fun σ _ => hσ σ)]`. Conclude with `product_formula hb`.
-/
theorem GlobalTheory.HtAdd.ProdFormulaPts.main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (x : Y.X), IsClosed ({x} : Set Y.X) →
    ∀ g : Y.Fn, UnitAt x g →
    (Function.support fun v : HeightOneSpectrum (𝓞 F) => if h : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), Real.log (h.some.w (valAt y.1 g)) else 0).Finite ∧
    (∑ σ : F →+* ℂ, ∑ᶠ (z : Pts Y σ) (_ : under z = x), Real.log ‖ratVal g z‖) +
      ∑ᶠ v : HeightOneSpectrum (𝓞 F), (if h : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), Real.log (h.some.w (valAt y.1 g)) else 0) = 0 := by
  intro F _ _ Y x hx g hg
  obtain ⟨a₀, hu, rfl⟩ := hg
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  obtain ⟨φ₀, hφ₀⟩ := Spec.map_surjective (Y.X.fromSpecResidueField x ≫ Y.str)
  have hfin : IsFinite (Spec.map φ₀) := by
    rw [hφ₀]
    exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  letI : Algebra F (Y.X.residueField x) := φ₀.hom.toAlgebra
  haveI : Module.Finite F (Y.X.residueField x) := (IsFinite.SpecMap_iff φ₀).1 hfin
  have hr : (Y.X.residue x).hom a₀ ≠ 0 := (hu.map (Y.X.residue x).hom).ne_zero
  have hb : Algebra.norm F ((Y.X.residue x).hom a₀) ≠ 0 := Algebra.norm_ne_zero_iff.2 hr
  have hfv : (fun v : HeightOneSpectrum (𝓞 F) => if h : Nonempty (Ext v) then
      ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), Real.log (h.some.w (GlobalTheory.TrueGeo.valAt y.1
        (algebraMap (Y.X.presheaf.stalk x) Y.X.functionField a₀))) else 0) =
      fun v => Real.log (HeightOneSpectrum.adicAbv F v (Algebra.norm F ((Y.X.residue x).hom a₀))) := by
    funext v
    have hne : Nonempty (Ext v) := (ExtConj.main F).1 v
    rw [dif_pos hne]
    refine (finsum_pts Y.str x φ₀ hφ₀ (algebraMap F (AlgebraicClosure F))
      (fun c => Real.log (hne.some.w c)) a₀).trans ?_
    refine (finsum_log (algebraMap F (AlgebraicClosure F)) hne.some.w.toMonoidWithZeroHom
      (fun c hc => (hne.some.w.pos hc).ne') hr).trans ?_
    exact congrArg Real.log (hne.some.w_alg _)
  have hσ : ∀ σ : F →+* ℂ, ∑ᶠ (z : Pts Y σ) (_ : under z = x),
      Real.log ‖ratVal (algebraMap (Y.X.presheaf.stalk x) Y.X.functionField a₀) z‖ =
        Real.log ‖σ (Algebra.norm F ((Y.X.residue x).hom a₀))‖ := by
    intro σ
    have e : ∑ᶠ (z : Pts Y σ) (_ : under z = x),
        Real.log ‖ratVal (algebraMap (Y.X.presheaf.stalk x) Y.X.functionField a₀) z‖ =
        ∑ᶠ (z : {z : Sp ℂ ⟶ Y.X // z ≫ Y.str = spMap σ}) (_ : below z.1 = x),
          Real.log ‖GlobalTheory.TrueGeo.valAt z.1 (algebraMap (Y.X.presheaf.stalk x) Y.X.functionField a₀)‖ := by
      refine finsum_congr fun z => finsum_congr fun hz => ?_
      have hreg : RegAt (under z) (algebraMap (Y.X.presheaf.stalk x) Y.X.functionField a₀) := by
        rw [hz]; exact ⟨a₀, rfl⟩
      rw [Res.ratVal_eq_valAt z hreg]
    refine e.trans ((finsum_pts Y.str x φ₀ hφ₀ σ (fun c => Real.log ‖c‖) a₀).trans ?_)
    exact finsum_log σ (normHom : ℂ →*₀ ℝ) (fun c hc => norm_ne_zero_iff.2 hc) hr
  refine ⟨?_, ?_⟩
  · rw [hfv]; exact finite_support_log_adicAbv hb
  · rw [hfv, Finset.sum_congr rfl (fun σ _ => hσ σ)]
    exact product_formula hb
