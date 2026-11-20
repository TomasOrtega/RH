import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAffineOpenOfFiniteOpensProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGaloisCoverOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperAndGeometricallyConnectedOfIsNilpotent
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyOfFinitePresentationOfCancelStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.TranslQuotient

/- English proof (translation)
Establish `h` using `GlobalTheory.isAmpleLB_of_relAmple A hL hamp U hU`. Conclude with `⟨fun s hs => by`. Take `⟨n, -, t, h1, -, h2⟩` from `h.exists_affine_finite_subset hs (U := ⊤) (Set.subset_univ _)`. Conclude with `⟨_, h2, h1⟩⟩`.
-/
theorem finiteSubsets_preimage {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (hL : L.IsLB)
    (hamp : Out.RelAmple A L) (U : S.Opens) (hU : IsAffineOpen U) :
    FiniteSubsetsInAffineOpens (A.hom ⁻¹ᵁ U) := by
  have h := GlobalTheory.isAmpleLB_of_relAmple A hL hamp U hU
  exact ⟨fun s hs => by
    obtain ⟨n, -, t, h1, -, h2⟩ := h.exists_affine_finite_subset hs (U := ⊤) (Set.subset_univ _)
    exact ⟨_, h2, h1⟩⟩

/- English proof (translation)
Simplify using `only [Hecke.transl, comp_mul, Category.id_comp, Category.comp_id]`. Rewrite using `[← Category.assoc, toUnit_unique (_ ≫ toUnit A) (toUnit A)]`. Conclude with `(mul_assoc _ _ _).symm`.
-/
theorem transl_mul {S : Scheme.{0}} {A : Over S} [GrpObj A] (a c : 𝟙_ (Over S) ⟶ A) :
    Hecke.transl (a * c) = Hecke.transl a ≫ Hecke.transl c := by
  simp only [Hecke.transl, comp_mul, Category.id_comp, Category.comp_id]
  rw [← Category.assoc, toUnit_unique (_ ≫ toUnit A) (toUnit A)]
  exact (mul_assoc _ _ _).symm

/- English proof (translation)
Simplify using `[Hecke.transl]`.
-/
theorem transl_one {S : Scheme.{0}} {A : Over S} [GrpObj A] :
    Hecke.transl (1 : 𝟙_ (Over S) ⟶ A) = 𝟙 A := by
  simp [Hecke.transl]

/- English proof (translation)
Use `hA.smooth` as an intermediate fact. Use `hA.proper` as an intermediate fact. Use `hA.geomConnected` as an intermediate fact. Establish `hw : q.left ≫ Q.hom = A.hom` using `Over.w q`. Use `GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected` as an intermediate fact.

Establish `: Flat (q.left ≫ Q.hom)` using `by rw [hw]; infer_instance`. Establish `: UniversallyClosed (q.left ≫ Q.hom)` using `by rw [hw]; infer_instance`. Establish `: IsSeparated (q.left ≫ Q.hom)` using `by rw [hw]; infer_instance`. Establish `: GeometricallyReduced (q.left ≫ Q.hom)` using `by rw [hw]; infer_instance`. Establish `: GeometricallyConnected (q.left ≫ Q.hom)` using `by rw [hw]; infer_instance`.

Establish `: LocallyOfFinitePresentation (q.left ≫ Q.hom)` using `by rw [hw]; infer_instance`. Use `GlobalTheory.flat_of_comp_of_flat_of_surjective q.left Q.hom` as an intermediate fact. Use `UniversallyClosed.of_comp_surjective q.left Q.hom` as an intermediate fact. Use `GlobalTheory.NilProper.isSeparated_of_comp_surjective q.left Q.hom` as an intermediate fact. Use `GlobalTheory.AbelianQuotient.geometricallyReduced_of_comp q.left Q.hom` as an intermediate fact.

Establish `: LocallyOfFinitePresentation Q.hom` using `GlobalTheory.T.locallyOfFinitePresentation_of_cancel q.left Q.hom hfin inferInstance inferInstance hsurj inferInstance`. Conclude with `⟨hQ, GlobalTheory.AbelianQuotient.smooth_of_grpObj_of_flat Q, ⟨⟩, GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp q.left Q.hom⟩`.
-/
theorem isAbelianScheme_of_finite_etale {S : Scheme.{0}} (A Q : Over S) [GrpObj A] [GrpObj Q]
    (q : A ⟶ Q) (hA : IsAbelianScheme A) (hQ : IsCommMonObj Q) (hfin : IsFinite q.left)
    (het : Etale q.left) (hsurj : Surjective q.left) : IsAbelianScheme Q := by
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hw : q.left ≫ Q.hom = A.hom := Over.w q
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : Flat (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : IsSeparated (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyReduced (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : LocallyOfFinitePresentation (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have := GlobalTheory.flat_of_comp_of_flat_of_surjective q.left Q.hom
  have := UniversallyClosed.of_comp_surjective q.left Q.hom
  have := GlobalTheory.NilProper.isSeparated_of_comp_surjective q.left Q.hom
  have := GlobalTheory.AbelianQuotient.geometricallyReduced_of_comp q.left Q.hom
  have : LocallyOfFinitePresentation Q.hom :=
    GlobalTheory.T.locallyOfFinitePresentation_of_cancel q.left Q.hom hfin inferInstance inferInstance hsurj inferInstance
  exact ⟨hQ, GlobalTheory.AbelianQuotient.smooth_of_grpObj_of_flat Q, ⟨⟩,
    GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp q.left Q.hom⟩

open GlobalTheory.AbelianQuotient in

/- English proof (translation)
Introduce `S A Q _ _ q _ _ _ hq`. Establish `hinv : ∀ {W : Over S} (a b : W ⟶ A), a ≫ q = b ≫ q → a⁻¹ ≫ q = b⁻¹ ≫ q`. Introduce `W a b h`. Establish `h1 : (a⁻¹ * a) ≫ q = (a⁻¹ * b) ≫ q` using `hq W _ _ _ _ rfl h`. Establish `h2` using `hq W b⁻¹ b⁻¹ (a⁻¹ * b) (a⁻¹ * a) rfl h1.symm`.

Establish `e1 : b⁻¹ * (a⁻¹ * b) = a⁻¹` using `by rw [mul_left_comm, inv_mul_cancel, _root_.mul_one]`. Establish `e2 : b⁻¹ * (a⁻¹ * a) = b⁻¹` using `by rw [inv_mul_cancel, _root_.mul_one]`. Rewrite `h2` using `[e1, e2]`. Then use the resulting hypothesis. Establish `hμ : ∀ {W : Over S} (x : W ⟶ A ⊗ A), x ≫ μ[A] = (x ≫ fst A A) * (x ≫ snd A A)`. Introduce `W x`.

Rewrite using `[Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]`. Use `flat_tensorHom q q` as an intermediate fact. Use `surjective_tensorHom q q` as an intermediate fact. Use `quasiCompact_tensorHom q q` as an intermediate fact. Use `FlatQuotient.epi_of_flat_surjective q` as an intermediate fact.

Use `FlatQuotient.epi_tensorHom q q` as an intermediate fact. Use `FlatQuotient.epi_tensorHom (q ⊗ₘ q) q` as an intermediate fact. Take `⟨m, hm⟩` from `exists_desc (q ⊗ₘ q) (μ[A] ≫ q) (by`. Introduce `W a b h`. Establish `h1 : (a ≫ fst A A) ≫ q = (b ≫ fst A A) ≫ q` using `by simpa using h =≫ fst Q Q`.

Establish `h2 : (a ≫ snd A A) ≫ q = (b ≫ snd A A) ≫ q` using `by simpa using h =≫ snd Q Q`. Rewrite using `[← Category.assoc, ← Category.assoc, hμ a, hμ b]`. Conclude with `hq W _ _ _ _ h1 h2)`. Take `⟨n, hn⟩` from `exists_desc q (GrpObj.inv ≫ q) (by`. Introduce `W a b h`.

Rewrite using `[← Category.assoc, ← Category.assoc, ← Hom.inv_def, ← Hom.inv_def]`. Conclude with `hinv a b h)`. Establish `key : ∀ {W : Over S} (a b : W ⟶ A), lift (a ≫ q) (b ≫ q) ≫ m = (a * b) ≫ q`. Introduce `W a b`. Rewrite using `[← lift_map, Category.assoc, hm, Hom.mul_def, Category.assoc]`.

Use `letI : MonObj Q := { one := η[A] ≫ q mul := m one_mul := by`. Rewrite using `[← cancel_epi (λ_ Q).inv, ← cancel_epi q]`. Use `key (1 : A ⟶ A) (𝟙 A)` as an intermediate fact. Rewrite `this` using `[_root_.one_mul]`. Rewrite using `[Iso.inv_hom_id, Category.comp_id]`.

Use `Eq.trans ?_ (this.trans (Category.id_comp _))` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Category.assoc]`. Use `congr 1`. Apply the tactic sequence `ext <;> simp [Hom.one_def]`. Use `mul_one := by`.

Rewrite using `[← cancel_epi (ρ_ Q).inv, ← cancel_epi q]`. Use `key (𝟙 A) (1 : A ⟶ A)` as an intermediate fact. Rewrite `this` using `[_root_.mul_one]`. Rewrite using `[Iso.inv_hom_id, Category.comp_id]`. Use `Eq.trans ?_ (this.trans (Category.id_comp _))` and prove the remaining obligations.

Rewrite using `[← Category.assoc, ← Category.assoc]`. Use `congr 1`. Apply the tactic sequence `ext <;> simp [Hom.one_def]`. Use `mul_assoc := by`. Rewrite using `[← cancel_epi ((q ⊗ₘ q) ⊗ₘ q)]`.

Establish `h1 : ((q ⊗ₘ q) ⊗ₘ q) ≫ m ▷ Q = (μ[A] ▷ A) ≫ (q ⊗ₘ q)`. Rewrite using `[← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hm, Category.comp_id, Category.id_comp]`. Establish `h2 : ((q ⊗ₘ q) ⊗ₘ q) ≫ (α_ Q Q Q).hom ≫ Q ◁ m = (α_ A A A).hom ≫ (A ◁ μ[A]) ≫ (q ⊗ₘ q)`. Rewrite using `[associator_naturality_assoc]`. Use `congr 1`.

Apply the tactic sequence `ext <;> simp [hm]`. Rewrite using `[reassoc_of% h1, reassoc_of% h2, hm, MonObj.mul_assoc_assoc] }`. Establish `hhom : IsMonHom q` using `⟨rfl, hm.symm⟩`. Use `letI : GrpObj Q := { inv := n left_inv := by`. Rewrite using `[← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]`.

Use `key GrpObj.inv (𝟙 A)` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Use `this.trans ?_` and prove the remaining obligations. Rewrite using `[Hom.mul_def, GrpObj.left_inv, comp_toUnit_assoc, Category.assoc]`. Both sides reduce to the same expression.

Use `right_inv := by`. Rewrite using `[← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]`. Use `key (𝟙 A) GrpObj.inv` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Use `this.trans ?_` and prove the remaining obligations.

Rewrite using `[Hom.mul_def, GrpObj.right_inv, comp_toUnit_assoc, Category.assoc]`. Use `rfl }`. Use `⟨inferInstance, ⟨?_⟩, hhom⟩` and prove the remaining obligations. Rewrite using `[← cancel_epi (q ⊗ₘ q), BraidedCategory.braiding_naturality_assoc, ← IsMonHom.mul_hom, IsCommMonObj.mul_comm_assoc]`.
-/
theorem grp_descent : ∀ (S : Scheme.{0}) (A Q : Over S) [GrpObj A] [IsCommMonObj A] (q : A ⟶ Q),
    Flat q.left → Surjective q.left → QuasiCompact q.left →
    (∀ (W : Over S) (a b c d : W ⟶ A), a ≫ q = b ≫ q → c ≫ q = d ≫ q → (a * c) ≫ q = (b * d) ≫ q) →
    ∃ _ : GrpObj Q, IsCommMonObj Q ∧ IsMonHom q := by
  intro S A Q _ _ q _ _ _ hq
  have hinv : ∀ {W : Over S} (a b : W ⟶ A), a ≫ q = b ≫ q → a⁻¹ ≫ q = b⁻¹ ≫ q := by
    intro W a b h
    have h1 : (a⁻¹ * a) ≫ q = (a⁻¹ * b) ≫ q := hq W _ _ _ _ rfl h
    have h2 := hq W b⁻¹ b⁻¹ (a⁻¹ * b) (a⁻¹ * a) rfl h1.symm
    have e1 : b⁻¹ * (a⁻¹ * b) = a⁻¹ := by rw [mul_left_comm, inv_mul_cancel, _root_.mul_one]
    have e2 : b⁻¹ * (a⁻¹ * a) = b⁻¹ := by rw [inv_mul_cancel, _root_.mul_one]
    rwa [e1, e2] at h2
  have hμ : ∀ {W : Over S} (x : W ⟶ A ⊗ A), x ≫ μ[A] = (x ≫ fst A A) * (x ≫ snd A A) := by
    intro W x
    rw [Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]
  have := flat_tensorHom q q
  have := surjective_tensorHom q q
  have := quasiCompact_tensorHom q q
  have := FlatQuotient.epi_of_flat_surjective q
  have := FlatQuotient.epi_tensorHom q q
  have := FlatQuotient.epi_tensorHom (q ⊗ₘ q) q
  obtain ⟨m, hm⟩ := exists_desc (q ⊗ₘ q) (μ[A] ≫ q) (by
    intro W a b h
    have h1 : (a ≫ fst A A) ≫ q = (b ≫ fst A A) ≫ q := by simpa using h =≫ fst Q Q
    have h2 : (a ≫ snd A A) ≫ q = (b ≫ snd A A) ≫ q := by simpa using h =≫ snd Q Q
    rw [← Category.assoc, ← Category.assoc, hμ a, hμ b]
    exact hq W _ _ _ _ h1 h2)
  obtain ⟨n, hn⟩ := exists_desc q (GrpObj.inv ≫ q) (by
    intro W a b h
    rw [← Category.assoc, ← Category.assoc, ← Hom.inv_def, ← Hom.inv_def]
    exact hinv a b h)
  have key : ∀ {W : Over S} (a b : W ⟶ A), lift (a ≫ q) (b ≫ q) ≫ m = (a * b) ≫ q := by
    intro W a b
    rw [← lift_map, Category.assoc, hm, Hom.mul_def, Category.assoc]
  letI : MonObj Q :=
    { one := η[A] ≫ q
      mul := m
      one_mul := by
        rw [← cancel_epi (λ_ Q).inv, ← cancel_epi q]
        have := key (1 : A ⟶ A) (𝟙 A)
        rw [_root_.one_mul] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_one := by
        rw [← cancel_epi (ρ_ Q).inv, ← cancel_epi q]
        have := key (𝟙 A) (1 : A ⟶ A)
        rw [_root_.mul_one] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_assoc := by
        rw [← cancel_epi ((q ⊗ₘ q) ⊗ₘ q)]
        have h1 : ((q ⊗ₘ q) ⊗ₘ q) ≫ m ▷ Q = (μ[A] ▷ A) ≫ (q ⊗ₘ q) := by
          rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
            hm, Category.comp_id, Category.id_comp]
        have h2 : ((q ⊗ₘ q) ⊗ₘ q) ≫ (α_ Q Q Q).hom ≫ Q ◁ m =
            (α_ A A A).hom ≫ (A ◁ μ[A]) ≫ (q ⊗ₘ q) := by
          rw [associator_naturality_assoc]
          congr 1
          ext <;> simp [hm]
        rw [reassoc_of% h1, reassoc_of% h2, hm, MonObj.mul_assoc_assoc] }
  have hhom : IsMonHom q := ⟨rfl, hm.symm⟩
  letI : GrpObj Q :=
    { inv := n
      left_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key GrpObj.inv (𝟙 A)
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.left_inv, comp_toUnit_assoc, Category.assoc]
        rfl
      right_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key (𝟙 A) GrpObj.inv
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.right_inv, comp_toUnit_assoc, Category.assoc]
        rfl }
  refine ⟨inferInstance, ⟨?_⟩, hhom⟩
  rw [← cancel_epi (q ⊗ₘ q), BraidedCategory.braiding_naturality_assoc, ← IsMonHom.mul_hom,
    IsCommMonObj.mul_comm_assoc]

/- English proof (translation)
Rewrite using `[Hecke.transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit A) (toUnit _)]`.
-/
theorem comp_transl {S : Scheme.{0}} {A W : Over S} [GrpObj A] (x : W ⟶ A) (h : 𝟙_ (Over S) ⟶ A) :
    x ≫ Hecke.transl h = x * (toUnit _ ≫ h) := by
  rw [Hecke.transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit A) (toUnit _)]

/- English proof (translation)
Introduce `S A Q _ _ H q hc W a b c d hab hcd`. Establish `loc` using `(GlobalTheory.ZM.galoisCover_descent _ _ _ _ _ hc).2.1`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `Scheme.hom_ext_of_forall _ _ fun p ↦ ?_` and prove the remaining obligations. Take `⟨V₁, h, hp₁, e₁⟩` from `loc W.left a.left b.left (congrArg CommaMorphism.left hab) p`.

Take `⟨V₂, k, hp₂, e₂⟩` from `loc W.left c.left d.left (congrArg CommaMorphism.left hcd) p`. Use `⟨V₁ ⊓ V₂, ⟨hp₁, hp₂⟩, ?_⟩` and prove the remaining obligations. Set `jV : Over.mk ((V₁ ⊓ V₂).ι ≫ W.hom) ⟶ W` to `Over.homMk (V₁ ⊓ V₂).ι rfl`. Establish `f₁ : jV ≫ b = (jV ≫ a) * (toUnit _ ≫ h.1)`. Rewrite using `[← comp_transl, Category.assoc]`.

Use `ext`. Simplify using `only [Over.comp_left, Over.homMk_left, jV]`. Rewrite using `[← W.left.homOfLE_ι (inf_le_left : V₁ ⊓ V₂ ≤ V₁), ]`. Simplify using `only [Category.assoc, e₁]`. Establish `f₂ : jV ≫ d = (jV ≫ c) * (toUnit _ ≫ k.1)`.

Rewrite using `[← comp_transl, Category.assoc]`. Use `ext`. Simplify using `only [Over.comp_left, Over.homMk_left, jV]`. Rewrite using `[← W.left.homOfLE_ι (inf_le_right : V₁ ⊓ V₂ ≤ V₂), ]`. Simplify using `only [Category.assoc, e₂]`.

Establish `hinv : Hecke.transl (h * k).1 ≫ q = q` using `Over.OverMorphism.ext (hc.inv (h * k))`. Establish `key : jV ≫ (b * d) = jV ≫ (a * c) ≫ Hecke.transl (h * k).1`. Rewrite using `[comp_mul, f₁, f₂, ← Category.assoc, comp_transl, comp_mul, Subgroup.coe_mul, comp_mul, _root_.mul_mul_mul_comm]`. Establish `key' : jV ≫ (a * c) ≫ q = jV ≫ (b * d) ≫ q`. Rewrite using `[← Category.assoc jV (b * d), key, Category.assoc, Category.assoc, hinv]`.

Simplify `congrArg CommaMorphism.left key'` using `[jV]`.
-/
theorem transl_compat : ∀ (S : Scheme.{0}) (A Q : Over S) [GrpObj A] [IsCommMonObj A]
    (H : Subgroup (𝟙_ (Over S) ⟶ A)) (q : A ⟶ Q),
    GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) q.left →
    ∀ (W : Over S) (a b c d : W ⟶ A), a ≫ q = b ≫ q → c ≫ q = d ≫ q → (a * c) ≫ q = (b * d) ≫ q := by
  intro S A Q _ _ H q hc W a b c d hab hcd
  have loc := (GlobalTheory.ZM.galoisCover_descent _ _ _ _ _ hc).2.1
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p ↦ ?_
  obtain ⟨V₁, h, hp₁, e₁⟩ := loc W.left a.left b.left (congrArg CommaMorphism.left hab) p
  obtain ⟨V₂, k, hp₂, e₂⟩ := loc W.left c.left d.left (congrArg CommaMorphism.left hcd) p
  refine ⟨V₁ ⊓ V₂, ⟨hp₁, hp₂⟩, ?_⟩
  let jV : Over.mk ((V₁ ⊓ V₂).ι ≫ W.hom) ⟶ W := Over.homMk (V₁ ⊓ V₂).ι rfl
  have f₁ : jV ≫ b = (jV ≫ a) * (toUnit _ ≫ h.1) := by
    rw [← comp_transl, Category.assoc]
    ext
    simp only [Over.comp_left, Over.homMk_left, jV]
    rw [← W.left.homOfLE_ι (inf_le_left : V₁ ⊓ V₂ ≤ V₁), ]
    simp only [Category.assoc, e₁]
  have f₂ : jV ≫ d = (jV ≫ c) * (toUnit _ ≫ k.1) := by
    rw [← comp_transl, Category.assoc]
    ext
    simp only [Over.comp_left, Over.homMk_left, jV]
    rw [← W.left.homOfLE_ι (inf_le_right : V₁ ⊓ V₂ ≤ V₂), ]
    simp only [Category.assoc, e₂]
  have hinv : Hecke.transl (h * k).1 ≫ q = q := Over.OverMorphism.ext (hc.inv (h * k))
  have key : jV ≫ (b * d) = jV ≫ (a * c) ≫ Hecke.transl (h * k).1 := by
    rw [comp_mul, f₁, f₂, ← Category.assoc, comp_transl, comp_mul, Subgroup.coe_mul, comp_mul,
      _root_.mul_mul_mul_comm]
  have key' : jV ≫ (a * c) ≫ q = jV ≫ (b * d) ≫ q := by
    rw [← Category.assoc jV (b * d), key, Category.assoc, Category.assoc, hinv]
  simpa [jV] using congrArg CommaMorphism.left key'

/- English proof (translation)
Introduce `S A _ _ L H hA hL hamp hH hfree`. Set `ρ : H → (A.left ⟶ A.left)` to `fun h => (Hecke.transl h.1).left`. Establish `h1 : ρ 1 = 𝟙 _` using `by show (Hecke.transl (1 : 𝟙_ (Over S) ⟶ A)).left = _`. Rewrite using `[transl_one]`. Both sides reduce to the same expression.

Establish `hm : ∀ a c, ρ (a * c) = ρ a ≫ ρ c` using `fun a c => by show (Hecke.transl (a.1 * c.1)).left = _`. Rewrite using `[transl_mul]`. Both sides reduce to the same expression. Establish `hS : ∀ a, ρ a ≫ A.hom = A.hom` using `fun a => Over.w _`. Set `τ` to `GlobalTheory.ZM.autOfRightAction ρ h1 hm`.

Establish `hτ : ∀ a, (τ a).hom ≫ A.hom = A.hom` using `fun a => hS a⁻¹`. Establish `: OrbitsInAffineOpens τ` using `OrbitsInAffineOpens.of_locally_on_base τ A.hom hτ fun s => by`. Take `⟨_, ⟨U, hU, rfl⟩, hsU, -⟩` from `S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ`. Conclude with `⟨U, hsU, finiteSubsets_preimage A L hL hamp U hU⟩`. Establish `hfreeρ : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Spec (.of k) ⟶ A.left) (a : H), y ≫ ρ a = y → a = 1`.

Introduce `k _ _ y a hy`. Set `y' : Over.mk (y ≫ A.hom) ⟶ A` to `Over.homMk y rfl`. Establish `e : y' ≫ Hecke.transl a.1 = y'` using `Over.OverMorphism.ext hy`. Establish `e' : y' ≫ Hecke.transl a.1 = y' * (toUnit _ ≫ a.1)`. Rewrite using `[Hecke.transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (y' ≫ toUnit A) (toUnit _)]`.

Rewrite `e` using `[e']`. Establish `h2 : toUnit (Over.mk (y ≫ A.hom)) ≫ a.1 = 1` using `mul_eq_left.mp e`. Conclude with `Subtype.ext (hfree k (y ≫ A.hom) a.1 a.2 h2)`. Establish `hf : IsFreeAction τ` using `.of_isAlgClosed fun k _ _ y a h ↦ inv_eq_one.mp (hfreeρ k y a⁻¹ h)`. Set `ψ : A ⟶ Over.mk (finiteQuotient.desc τ A.hom hτ)` to `Over.homMk (finiteQuotient.π τ) (finiteQuotient.π_desc τ A.hom hτ)`.

Establish `hc : GlobalTheory.ZM.IsGaloisCover H ρ ψ.left`. Use `⟨hH, h1, hm, fun a ↦ ?_, finiteQuotient.isFinite_π_of_isFreeAction hf, finiteQuotient.etale_π hf, inferInstanceAs (Surjective (finiteQuotient.π τ)), fun k _ _ y y' e ↦ ?_⟩` and prove the remaining obligations. Use `finiteQuotient.comp_π τ a⁻¹` as an intermediate fact. Rewrite `this` using `[GlobalTheory.ZM.autOfRightAction_hom, inv_inv]`. Then use the resulting hypothesis. Take `⟨a, ha⟩` from `(finiteQuotient.comp_π_eq_iff τ y y').mp e`.

Establish `ha : y ≫ ρ a⁻¹ = y'` using `ha`. Use `⟨a⁻¹, ha, fun c hc ↦ ?_⟩` and prove the remaining obligations. Establish `hc : y ≫ ρ c = y'` using `hc`. Establish `: y ≫ ρ (c * a) = y`. Rewrite using `[hm, reassoc_of% hc, ← ha, Category.assoc, ← hm, inv_mul_cancel, h1, Category.comp_id]`.

Conclude with `eq_inv_of_mul_eq_one_left (hfreeρ k y _ this)`. Use `hc.fin` as an intermediate fact. Use `hc.etale` as an intermediate fact. Use `hc.onto` as an intermediate fact. Take `⟨inst, hcomm, hhom⟩` from `grp_descent S A _ ψ inferInstance hc.onto inferInstance (transl_compat S A _ H ψ hc)`.

Conclude with `⟨_, inst, hcomm, ψ, isAbelianScheme_of_finite_etale A _ ψ hA hcomm hc.fin hc.etale hc.onto, hhom, hc⟩`.
-/
theorem exists_quotient : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (H : Subgroup (𝟙_ (Over S) ⟶ A)), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Finite H → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ A), h ∈ H → toUnit (Over.mk x) ≫ h = 1 → h = 1) → ∃ (A' : Over S) (_ : GrpObj A') (_ : IsCommMonObj A') (ψ : A ⟶ A'), IsAbelianScheme A' ∧ IsMonHom ψ ∧ GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left := by
  intro S A _ _ L H hA hL hamp hH hfree
  let ρ : H → (A.left ⟶ A.left) := fun h => (Hecke.transl h.1).left
  have h1 : ρ 1 = 𝟙 _ := by
    show (Hecke.transl (1 : 𝟙_ (Over S) ⟶ A)).left = _
    rw [transl_one]; rfl
  have hm : ∀ a c, ρ (a * c) = ρ a ≫ ρ c := fun a c => by
    show (Hecke.transl (a.1 * c.1)).left = _
    rw [transl_mul]; rfl
  have hS : ∀ a, ρ a ≫ A.hom = A.hom := fun a => Over.w _
  let τ := GlobalTheory.ZM.autOfRightAction ρ h1 hm
  have hτ : ∀ a, (τ a).hom ≫ A.hom = A.hom := fun a => hS a⁻¹
  have : OrbitsInAffineOpens τ := OrbitsInAffineOpens.of_locally_on_base τ A.hom hτ fun s => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
    exact ⟨U, hsU, finiteSubsets_preimage A L hL hamp U hU⟩
  have hfreeρ : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Spec (.of k) ⟶ A.left) (a : H),
      y ≫ ρ a = y → a = 1 := by
    intro k _ _ y a hy
    let y' : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y rfl
    have e : y' ≫ Hecke.transl a.1 = y' := Over.OverMorphism.ext hy
    have e' : y' ≫ Hecke.transl a.1 = y' * (toUnit _ ≫ a.1) := by
      rw [Hecke.transl, comp_mul, Category.comp_id, ← Category.assoc,
        toUnit_unique (y' ≫ toUnit A) (toUnit _)]
    rw [e'] at e
    have h2 : toUnit (Over.mk (y ≫ A.hom)) ≫ a.1 = 1 := mul_eq_left.mp e
    exact Subtype.ext (hfree k (y ≫ A.hom) a.1 a.2 h2)
  have hf : IsFreeAction τ := .of_isAlgClosed fun k _ _ y a h ↦ inv_eq_one.mp (hfreeρ k y a⁻¹ h)
  let ψ : A ⟶ Over.mk (finiteQuotient.desc τ A.hom hτ) :=
    Over.homMk (finiteQuotient.π τ) (finiteQuotient.π_desc τ A.hom hτ)
  have hc : GlobalTheory.ZM.IsGaloisCover H ρ ψ.left := by
    refine ⟨hH, h1, hm, fun a ↦ ?_, finiteQuotient.isFinite_π_of_isFreeAction hf,
      finiteQuotient.etale_π hf, inferInstanceAs (Surjective (finiteQuotient.π τ)),
      fun k _ _ y y' e ↦ ?_⟩
    · have := finiteQuotient.comp_π τ a⁻¹
      rwa [GlobalTheory.ZM.autOfRightAction_hom, inv_inv] at this
    · obtain ⟨a, ha⟩ := (finiteQuotient.comp_π_eq_iff τ y y').mp e
      have ha : y ≫ ρ a⁻¹ = y' := ha
      refine ⟨a⁻¹, ha, fun c hc ↦ ?_⟩
      have hc : y ≫ ρ c = y' := hc
      have : y ≫ ρ (c * a) = y := by
        rw [hm, reassoc_of% hc, ← ha, Category.assoc, ← hm, inv_mul_cancel, h1, Category.comp_id]
      exact eq_inv_of_mul_eq_one_left (hfreeρ k y _ this)
  have := hc.fin
  have := hc.etale
  have := hc.onto
  obtain ⟨inst, hcomm, hhom⟩ := grp_descent S A _ ψ inferInstance hc.onto inferInstance
    (transl_compat S A _ H ψ hc)
  exact ⟨_, inst, hcomm, ψ, isAbelianScheme_of_finite_etale A _ ψ hA hcomm hc.fin hc.etale hc.onto,
    hhom, hc⟩

end GlobalTheory.TranslQuotient

end
