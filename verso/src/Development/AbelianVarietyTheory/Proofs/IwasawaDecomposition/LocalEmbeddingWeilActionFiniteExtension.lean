import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupAtPlaceDenseInDecompositionGroupStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocDec

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

/- English proof (translation)
Establish `: IsGalois E Ω` using `IsAlgClosure.isGalois E Ω`. Use `set d := θ.symm g with hd`. Set `S : Set (Dec (F` to `E) A) := (fun σ => g⁻¹ * θ σ) ⁻¹' (H : Set (GalLoc w))`. Establish `hS : IsOpen S` using `hH.preimage (continuous_const.mul hθ)`. Establish `hdS : d ∈ S` using `by show g⁻¹ * θ d ∈ H`.

Rewrite using `[hd, MulEquiv.apply_symm_apply, inv_mul_cancel]`. Conclude with `H.one_mem`. Take `⟨t, ht, hts⟩` from `isOpen_induced_iff.mp hS`. Establish `hdt : (d : G E Ω) ∈ t`. Rewrite `hdS` using `[← hts]`.

Conclude with `hdS`. Establish `hnhds : {x : G E Ω | (d : G E Ω) * x ∈ t} ∈ nhds (1 : G E Ω)`. Apply `(continuous_mul_left (d : G E Ω)).continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Simplify using `using ht.mem_nhds hdt`. Take `⟨F, hF, hFs⟩` from `(krullTopology_mem_nhds_one_iff E Ω _).mp hnhds`.

Set `pb` to `Field.powerBasisOfFiniteOfSeparable E F`. Take `⟨τ, hτW, hτ⟩` from `GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup E Ω A w h (d : G E Ω) d.2 (pb.gen : Ω)`. Establish `hfix : (d : G E Ω)⁻¹ * τ ∈ F.fixingSubgroup`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`.

Establish `e : (((d : G E Ω)⁻¹ * τ : G E Ω) : Ω →ₐ[E] Ω).comp F.val = F.val` using `pb.algHom_ext (by show ((d : G E Ω)⁻¹ * τ) (pb.gen : Ω) = pb.gen`. Rewrite using `[AlgEquiv.mul_apply, hτ]`. Use `show ((d : G E Ω)⁻¹ * (d : G E Ω)) (pb.gen : Ω) = pb.gen`. Use the proof step `simp)`. Conclude with `congrArg (fun φ : F →ₐ[E] Ω => φ ⟨x, hx⟩) e`.

Establish `hτt : τ ∈ t`. Use `hFs hfix` as an intermediate fact. Simplify using `using this`. Set `σ : Dec (F` to `E) A := ⟨τ, Weil_le_Dec h hτW⟩`. Establish `hσS : σ ∈ S`.

Rewrite using `[← hts]`. Conclude with `hτt`. Conclude with `⟨⟨τ, hτW⟩, θ σ, hl σ, hσS⟩`.
-/
theorem exists_lifts_mul_mem (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (ι : Ω →ₐ[E] Kbar w) (θ : Dec (F := E) A ≃* GalLoc w) (hθ : Continuous θ)
    (hl : ∀ σ : Dec (F := E) A, Lifts ι (θ σ) (σ : G E Ω)) (g : GalLoc w) (H : Subgroup (GalLoc w))
    (hH : IsOpen (H : Set (GalLoc w))) :
    ∃ (σ : Weil h) (g' : GalLoc w), Lifts ι g' (σ : G E Ω) ∧ g⁻¹ * g' ∈ H := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  set d := θ.symm g with hd
  let S : Set (Dec (F := E) A) := (fun σ => g⁻¹ * θ σ) ⁻¹' (H : Set (GalLoc w))
  have hS : IsOpen S := hH.preimage (continuous_const.mul hθ)
  have hdS : d ∈ S := by
    show g⁻¹ * θ d ∈ H
    rw [hd, MulEquiv.apply_symm_apply, inv_mul_cancel]
    exact H.one_mem
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp hS
  have hdt : (d : G E Ω) ∈ t := by
    rw [← hts] at hdS
    exact hdS
  have hnhds : {x : G E Ω | (d : G E Ω) * x ∈ t} ∈ nhds (1 : G E Ω) := by
    apply (continuous_mul_left (d : G E Ω)).continuousAt.preimage_mem_nhds
    simpa using ht.mem_nhds hdt
  obtain ⟨F, hF, hFs⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp hnhds
  let pb := Field.powerBasisOfFiniteOfSeparable E F
  obtain ⟨τ, hτW, hτ⟩ := GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup E Ω A w h (d : G E Ω) d.2 (pb.gen : Ω)
  have hfix : (d : G E Ω)⁻¹ * τ ∈ F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have e : (((d : G E Ω)⁻¹ * τ : G E Ω) : Ω →ₐ[E] Ω).comp F.val = F.val := pb.algHom_ext (by
      show ((d : G E Ω)⁻¹ * τ) (pb.gen : Ω) = pb.gen
      rw [AlgEquiv.mul_apply, hτ]
      show ((d : G E Ω)⁻¹ * (d : G E Ω)) (pb.gen : Ω) = pb.gen
      simp)
    exact congrArg (fun φ : F →ₐ[E] Ω => φ ⟨x, hx⟩) e
  have hτt : τ ∈ t := by
    have := hFs hfix
    simpa using this
  let σ : Dec (F := E) A := ⟨τ, Weil_le_Dec h hτW⟩
  have hσS : σ ∈ S := by
    rw [← hts]
    exact hτt
  exact ⟨⟨τ, hτW⟩, θ σ, hl σ, hσS⟩

end GlobalTheory.LocDec

namespace GlobalTheory.LocDec

/- English proof (translation)
Take `⟨θ, hθ, -, hl⟩` from `decomposition_mulEquiv_galLoc E Ω A w h ι hι`. Use `set Kw := w.adicCompletion E`. Establish `: CharZero Kw` using `charZero_of_injective_algebraMap (algebraMap E Kw).injective`. Establish `: IsGalois Kw (Kbar w)` using `IsAlgClosure.isGalois Kw (Kbar w)`. Use `set M := IntermediateField.adjoin Kw (Set.range fun x : K => ι (algebraMap K Ω x)) with hM`.

Establish `hfx : ∀ (σ : G E Ω) (g' : GalLoc w), Lifts ι g' σ → ∀ x : K, (g' (ι (algebraMap K Ω x)) = ι (algebraMap K Ω x) ↔ σ (algebraMap K Ω x) = algebraMap K Ω x)` using `fun σ g' hg x => by rw [hg]; exact ι.toRingHom.injective.eq_iff`. Establish `: FiniteDimensional E K` using `Module.Finite.of_restrictScalars_finite ℚ E K`. Set `pb` to `Field.powerBasisOfFiniteOfSeparable E K`. Establish `hprim : ∀ σ : G E Ω, σ (algebraMap K Ω pb.gen) = algebraMap K Ω pb.gen → ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x`. Introduce `σ hσ x`.

Establish `e : ((σ : Ω →ₐ[E] Ω).comp (IsScalarTower.toAlgHom E K Ω)) = IsScalarTower.toAlgHom E K Ω` using `pb.algHom_ext (by simpa using hσ)`. Simplify using `using congrArg (fun φ : K →ₐ[E] Ω => φ x) e`. Establish `hopen : ∀ z : Kbar w, IsOpen ((IntermediateField.adjoin Kw {z}).fixingSubgroup : Set (GalLoc w))` using `fun z => by`. Establish `: FiniteDimensional Kw (IntermediateField.adjoin Kw {z})` using `IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)`. Conclude with `IntermediateField.fixingSubgroup_isOpen _`.

Establish `hmemz : ∀ (z : Kbar w) (k : GalLoc w), k ∈ (IntermediateField.adjoin Kw {z}).fixingSubgroup → k z = z` using `fun z k hk => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk z (IntermediateField.mem_adjoin_simple_self _ _)`. Establish `hLopen : IsOpen (L.fixingSubgroup : Set (GalLoc w))` using `IntermediateField.fixingSubgroup_isOpen L`. Establish `hLfix : ∀ k : GalLoc w, k ∈ L.fixingSubgroup → ∀ z ∈ L, k z = z` using `fun k hk => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `z hz`.

Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup M, IntermediateField.mem_fixedField_iff]`. Introduce `g hg`. Establish `hga : g (ι (algebraMap K Ω pb.gen)) = ι (algebraMap K Ω pb.gen)` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ (IntermediateField.subset_adjoin _ _ ⟨pb.gen, rfl⟩)`. Take `⟨σ, g', hlift, hk⟩` from `exists_lifts_mul_mem A w h ι θ hθ hl g (L.fixingSubgroup ⊓ (IntermediateField.adjoin Kw {ι (algebraMap K Ω pb.gen)}).fixingSubgroup) (hLopen.inter (hopen _))`. Establish `hg' : g' = g * (g⁻¹ * g')` using `by group`.

Establish `h1 : g' (ι (algebraMap K Ω pb.gen)) = ι (algebraMap K Ω pb.gen)`. Rewrite using `[hg', AlgEquiv.mul_apply, hmemz _ _ (Subgroup.mem_inf.1 hk).2, hga]`. Establish `h2` using `hprim σ ((hfx σ g' hlift pb.gen).1 h1)`. Establish `h3` using `(hfix σ g' hlift).2 h2 z hz`. Rewrite `h3` using `[hg', AlgEquiv.mul_apply, hLfix _ (Subgroup.mem_inf.1 hk).1 z hz]`.

Conclude with `h3`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup L]`. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixedField_iff]`.

Introduce `g hg`. Take `⟨σ, g', hlift, hk⟩` from `exists_lifts_mul_mem A w h ι θ hθ hl g (L.fixingSubgroup ⊓ (IntermediateField.adjoin Kw {ι (algebraMap K Ω x)}).fixingSubgroup) (hLopen.inter (hopen _))`. Establish `hg' : g' = g * (g⁻¹ * g')` using `by group`. Establish `h1 : ∀ z ∈ L, g' z = z` using `fun z hz => by`. Rewrite using `[hg', AlgEquiv.mul_apply, hLfix _ (Subgroup.mem_inf.1 hk).1 z hz, hLfix g hg z hz]`.

Establish `h2` using `(hfx σ g' hlift x).2 ((hfix σ g' hlift).1 h1 x)`. Rewrite `h2` using `[hg', AlgEquiv.mul_apply, hmemz _ _ (Subgroup.mem_inf.1 hk).2]`. Conclude with `h2`.
-/
theorem eq_adjoin_of_fixing_iff (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [Algebra E K] [IsScalarTower E K Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w)
    (hι : IsLocEmb A w ι) (L : IntermediateField (w.adicCompletion E) (Kbar w))
    [FiniteDimensional (w.adicCompletion E) L]
    (hfix : ∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ →
      ((∀ z ∈ L, g z = z) ↔ ∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x)) :
    L = IntermediateField.adjoin (w.adicCompletion E) (Set.range fun x : K => ι (algebraMap K Ω x)) := by
  obtain ⟨θ, hθ, -, hl⟩ := decomposition_mulEquiv_galLoc E Ω A w h ι hι
  set Kw := w.adicCompletion E
  have : CharZero Kw := charZero_of_injective_algebraMap (algebraMap E Kw).injective
  have : IsGalois Kw (Kbar w) := IsAlgClosure.isGalois Kw (Kbar w)
  set M := IntermediateField.adjoin Kw (Set.range fun x : K => ι (algebraMap K Ω x)) with hM
  have hfx : ∀ (σ : G E Ω) (g' : GalLoc w), Lifts ι g' σ → ∀ x : K,
      (g' (ι (algebraMap K Ω x)) = ι (algebraMap K Ω x) ↔ σ (algebraMap K Ω x) = algebraMap K Ω x) :=
    fun σ g' hg x => by rw [hg]; exact ι.toRingHom.injective.eq_iff
  have : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
  let pb := Field.powerBasisOfFiniteOfSeparable E K
  have hprim : ∀ σ : G E Ω, σ (algebraMap K Ω pb.gen) = algebraMap K Ω pb.gen →
      ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x := by
    intro σ hσ x
    have e : ((σ : Ω →ₐ[E] Ω).comp (IsScalarTower.toAlgHom E K Ω)) = IsScalarTower.toAlgHom E K Ω :=
      pb.algHom_ext (by simpa using hσ)
    simpa using congrArg (fun φ : K →ₐ[E] Ω => φ x) e
  have hopen : ∀ z : Kbar w,
      IsOpen ((IntermediateField.adjoin Kw {z}).fixingSubgroup : Set (GalLoc w)) := fun z => by
    have : FiniteDimensional Kw (IntermediateField.adjoin Kw {z}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
    exact IntermediateField.fixingSubgroup_isOpen _
  have hmemz : ∀ (z : Kbar w) (k : GalLoc w), k ∈ (IntermediateField.adjoin Kw {z}).fixingSubgroup → k z = z :=
    fun z k hk => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk z (IntermediateField.mem_adjoin_simple_self _ _)
  have hLopen : IsOpen (L.fixingSubgroup : Set (GalLoc w)) := IntermediateField.fixingSubgroup_isOpen L
  have hLfix : ∀ k : GalLoc w, k ∈ L.fixingSubgroup → ∀ z ∈ L, k z = z :=
    fun k hk => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  apply le_antisymm
  · intro z hz
    rw [← InfiniteGalois.fixedField_fixingSubgroup M, IntermediateField.mem_fixedField_iff]
    intro g hg
    have hga : g (ι (algebraMap K Ω pb.gen)) = ι (algebraMap K Ω pb.gen) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _
        (IntermediateField.subset_adjoin _ _ ⟨pb.gen, rfl⟩)
    obtain ⟨σ, g', hlift, hk⟩ := exists_lifts_mul_mem A w h ι θ hθ hl g
      (L.fixingSubgroup ⊓ (IntermediateField.adjoin Kw {ι (algebraMap K Ω pb.gen)}).fixingSubgroup)
      (hLopen.inter (hopen _))
    have hg' : g' = g * (g⁻¹ * g') := by group
    have h1 : g' (ι (algebraMap K Ω pb.gen)) = ι (algebraMap K Ω pb.gen) := by
      rw [hg', AlgEquiv.mul_apply, hmemz _ _ (Subgroup.mem_inf.1 hk).2, hga]
    have h2 := hprim σ ((hfx σ g' hlift pb.gen).1 h1)
    have h3 := (hfix σ g' hlift).2 h2 z hz
    rw [hg', AlgEquiv.mul_apply, hLfix _ (Subgroup.mem_inf.1 hk).1 z hz] at h3
    exact h3
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    rw [← InfiniteGalois.fixedField_fixingSubgroup L]
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro g hg
    obtain ⟨σ, g', hlift, hk⟩ := exists_lifts_mul_mem A w h ι θ hθ hl g
      (L.fixingSubgroup ⊓ (IntermediateField.adjoin Kw {ι (algebraMap K Ω x)}).fixingSubgroup)
      (hLopen.inter (hopen _))
    have hg' : g' = g * (g⁻¹ * g') := by group
    have h1 : ∀ z ∈ L, g' z = z := fun z hz => by
      rw [hg', AlgEquiv.mul_apply, hLfix _ (Subgroup.mem_inf.1 hk).1 z hz, hLfix g hg z hz]
    have h2 := (hfx σ g' hlift x).2 ((hfix σ g' hlift).1 h1 x)
    rw [hg', AlgEquiv.mul_apply, hmemz _ _ (Subgroup.mem_inf.1 hk).2] at h2
    exact h2

/- English proof (translation)
Introduce `E K Ω _ _ _ _ _ _ _ _ _ _ _ A w h ι hι L _ hfix`. Conclude with `eq_adjoin_of_fixing_iff E K Ω A w h ι hι L hfix`.
-/
theorem eq_adjoin_of_fixing_iff_weil : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ L : IntermediateField (w.adicCompletion E) (Kbar w), FiniteDimensional (w.adicCompletion E) L → (∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ → ((∀ z ∈ L, g z = z) ↔ ∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x)) → L = IntermediateField.adjoin (w.adicCompletion E) (Set.range fun x : K => ι (algebraMap K Ω x)) := by
  intro E K Ω _ _ _ _ _ _ _ _ _ _ _ A w h ι hι L _ hfix
  exact eq_adjoin_of_fixing_iff E K Ω A w h ι hι L hfix

end GlobalTheory.LocDec
