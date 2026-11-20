import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ChainOnto.LStab
section General
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Rewrite using `[hβ]`. Introduce `k`. Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]`. Use `split_ifs`. Conclude with `Subring.one_mem _`.

Conclude with `Subring.zero_mem _`.
-/
theorem col_mem_hatL {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hβ : IsFrame β Λ)
    (j : Fin n) : β.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  rw [hβ]
  intro k
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

/- English proof (translation)
Establish `hcol : ∀ j, ∃ T : Finset (Fin n → E ⊗[F] Formalism.L2.Herm.Af F), (T : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) ⊆ (fun x : Fin n → E => fun i => Formalism.UG.inclE (F` using `F) (Formalism.L2.Herm.Af F) (x i)) '' (Λ : Set (Fin n → E)) ∧ β.1 *ᵥ Pi.single j 1 ∈ Submodule.span (Formalism.L2.Herm.intAf F E) (T : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) := fun j => Submodule.mem_span_finite_of_mem_span (col_mem_hatL hβ j)`. Use `choose T hT hmem using hcol`. Set `U : Finset (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)` to `Finset.univ.biUnion T`. Establish `hUsub : ∀ y ∈ U, ∃ x ∈ Λ, (fun i => Formalism.UG.inclE (F` using `F) (Formalism.L2.Herm.Af F) (x i)) = y := fun y hy => by`. Take `⟨j, -, hj⟩` from `Finset.mem_biUnion.1 hy`.

Take `⟨x, hx, e⟩` from `hT j hj`. Conclude with `⟨x, hx, e⟩`. Use `choose! pre hpre hpref using hUsub`. Establish `hle : Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F))) ≤ Λ`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hpre y hy`. Use `⟨Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F))), hle, Submodule.fg_def.2 ⟨_, (U.finite_toSet.image pre), rfl⟩, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Conclude with `⟨x, hle hx, rfl⟩`. Establish `hcolm : ∀ j, β.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F` using `F) (Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)))) := by`. Introduce `j`. Use `Submodule.span_mono ?_ (hmem j)` and prove the remaining obligations. Introduce `y hy`.

Establish `hyU : y ∈ U` using `Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hy⟩`. Conclude with `⟨pre y, Submodule.subset_span ⟨y, hyU, rfl⟩, hpref y hyU⟩`. Introduce `y hy`. Establish `hc` using `(hβ y).1 hy`. Take `⟨c, hcdef⟩ : ∃ c, c = (β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1 *ᵥ y` from `⟨_, rfl⟩`.

Rewrite `hc` using `[← hcdef]`. Establish `ey : y = ∑ j, c j • (β.1 *ᵥ Pi.single j 1)`. Establish `e1 : y = β.1 *ᵥ c`. Rewrite using `[hcdef, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Establish `e2 : c = ∑ j, c j • (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)`.

Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[e1]`. Use `conv_lhs => rw [e2]`. Rewrite using `[Matrix.mulVec_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => Matrix.mulVec_smul _ _ _`. Rewrite using `[ey]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ (⟨c j, hc j⟩ : Formalism.L2.Herm.intAf F E) (hcolm j)`.
-/
theorem exists_fg_sub {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hβ : IsFrame β Λ) :
    ∃ Λ₁ ≤ Λ, Λ₁.FG ∧ Formalism.L2.Herm.hatL (F := F) Λ₁ = Formalism.L2.Herm.hatL (F := F) Λ := by
  classical
  have hcol : ∀ j, ∃ T : Finset (Fin n → E ⊗[F] Formalism.L2.Herm.Af F),
      (T : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) ⊆ (fun x : Fin n → E => fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) '' (Λ : Set (Fin n → E)) ∧
      β.1 *ᵥ Pi.single j 1 ∈ Submodule.span (Formalism.L2.Herm.intAf F E) (T : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) := fun j =>
    Submodule.mem_span_finite_of_mem_span (col_mem_hatL hβ j)
  choose T hT hmem using hcol
  let U : Finset (Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := Finset.univ.biUnion T
  have hUsub : ∀ y ∈ U, ∃ x ∈ Λ, (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) = y := fun y hy => by
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hy
    obtain ⟨x, hx, e⟩ := hT j hj
    exact ⟨x, hx, e⟩
  choose! pre hpre hpref using hUsub
  have hle : Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F))) ≤ Λ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact hpre y hy
  refine ⟨Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F))), hle,
    Submodule.fg_def.2 ⟨_, (U.finite_toSet.image pre), rfl⟩, le_antisymm ?_ ?_⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hle hx, rfl⟩
  · have hcolm : ∀ j, β.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := F) (Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)))) := by
      intro j
      refine Submodule.span_mono ?_ (hmem j)
      intro y hy
      have hyU : y ∈ U := Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hy⟩
      exact ⟨pre y, Submodule.subset_span ⟨y, hyU, rfl⟩, hpref y hyU⟩
    intro y hy
    have hc := (hβ y).1 hy
    obtain ⟨c, hcdef⟩ : ∃ c, c = (β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1 *ᵥ y := ⟨_, rfl⟩
    rw [← hcdef] at hc
    have ey : y = ∑ j, c j • (β.1 *ᵥ Pi.single j 1) := by
      have e1 : y = β.1 *ᵥ c := by
        rw [hcdef, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have e2 : c = ∑ j, c j • (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply]
      rw [e1]
      conv_lhs => rw [e2]
      rw [Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun j _ => Matrix.mulVec_smul _ _ _
    rw [ey]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem _ (⟨c j, hc j⟩ : Formalism.L2.Herm.intAf F E) (hcolm j)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Conclude with `GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => GlobalTheory.AdelicU.tmul_mem_latLoc ha (hle hx)) (zero_mem _) (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy`. Introduce `y hy`. Use `GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => ?_) (zero_mem _) (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy` and prove the remaining obligations.

Establish `h1 : (fun i => Formalism.UG.inclE (F` using `F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ₁ := heq ▸ Submodule.subset_span ⟨x, hx, rfl⟩`. Establish `h2 : (fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ₁ : Set (Fin n → E))` using `(GlobalTheory.LevSplit.latHat_iff Λ₁ _).2 h1`. Establish `h3` using `(GlobalTheory.AdelicU.mem_latHat_iff hfg _).1 h2 v`. Establish `h4 : GlobalTheory.AdelicU.vecLoc v (fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x i) = fun i => (1 : Fv F v) ⊗ₜ[F] x i`. Use function extensionality and compare the values at `i`.

Simplify using `[GlobalTheory.AdelicU.vecLoc]`. Rewrite `h3` using `[h4]`. Establish `h5` using `(GlobalTheory.AdelicU.latLoc F Λ₁ v).smul_mem ⟨a ⊗ₜ[F] ((1 : 𝓞 E) : E), GlobalTheory.AdelicU.tmul_mem_intLoc ha 1⟩ h3`. Use `h5 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Use `show _ = (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] x i)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Simplify using the standard rewrite rules.
-/
theorem latLoc_eq {Λ₁ Λ : Submodule (𝓞 E) (Fin n → E)} (hle : Λ₁ ≤ Λ) (hfg : Λ₁.FG)
    (heq : Formalism.L2.Herm.hatL (F := F) Λ₁ = Formalism.L2.Herm.hatL (F := F) Λ) (v : HeightOneSpectrum (𝓞 F)) :
    GlobalTheory.AdelicU.latLoc F Λ₁ v = GlobalTheory.AdelicU.latLoc F Λ v := by
  apply le_antisymm
  · intro y hy
    exact GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => GlobalTheory.AdelicU.tmul_mem_latLoc ha (hle hx)) (zero_mem _)
      (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy
  · intro y hy
    refine GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => ?_) (zero_mem _)
      (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy
    have h1 : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ₁ :=
      heq ▸ Submodule.subset_span ⟨x, hx, rfl⟩
    have h2 : (fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ₁ : Set (Fin n → E)) :=
      (GlobalTheory.LevSplit.latHat_iff Λ₁ _).2 h1
    have h3 := (GlobalTheory.AdelicU.mem_latHat_iff hfg _).1 h2 v
    have h4 : GlobalTheory.AdelicU.vecLoc v (fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x i) = fun i => (1 : Fv F v) ⊗ₜ[F] x i := by
      funext i
      simp [GlobalTheory.AdelicU.vecLoc]
    rw [h4] at h3
    have h5 := (GlobalTheory.AdelicU.latLoc F Λ₁ v).smul_mem
      ⟨a ⊗ₜ[F] ((1 : 𝓞 E) : E), GlobalTheory.AdelicU.tmul_mem_intLoc ha 1⟩ h3
    convert h5 using 1
    funext i
    show _ = (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] x i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp

end General

section Adelic
variable {D : D7}

/- English proof (translation)
Establish `h1` using `GlobalTheory.LevSplit.mem_St_iff β Λ hfr (Lev.finE V g)`. Establish `h2` using `GlobalTheory.LevSplit.stab_gen (GlobalTheory.LevSplit.swp D.host.F D.host.E) GlobalTheory.LevSplit.swp_bij.2 _ _ (GlobalTheory.LevSplit.latHat_iff Λ) (finHom V g)`. Establish `h3` using `GlobalTheory.AdelicU.mem_levelOpen_iff_latHat D.sp.cm.sig V.gram hfg g`. Establish `h4` using `GlobalTheory.AdelicU.mem_levelOpen (σ := D.sp.cm.sig) (J := V.gram) (L := Λ) (g := g)`. Conclude with `h1.trans (h2.symm.trans (h3.symm.trans h4))`.
-/
theorem finE_mem_St_iff_of_fg (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (hfg : Λ.FG) (g : GA D V) :
    Lev.finE V g ∈ Formalism.L2.DIV.St β ↔
      ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := by
  have h1 := GlobalTheory.LevSplit.mem_St_iff β Λ hfr (Lev.finE V g)
  have h2 := GlobalTheory.LevSplit.stab_gen (GlobalTheory.LevSplit.swp D.host.F D.host.E) GlobalTheory.LevSplit.swp_bij.2 _ _
    (GlobalTheory.LevSplit.latHat_iff Λ) (finHom V g)
  have h3 := GlobalTheory.AdelicU.mem_levelOpen_iff_latHat D.sp.cm.sig V.gram hfg g
  have h4 := GlobalTheory.AdelicU.mem_levelOpen (σ := D.sp.cm.sig) (J := V.gram) (L := Λ) (g := g)
  exact h1.trans (h2.symm.trans (h3.symm.trans h4))

end Adelic

/- English proof (translation)
Introduce `D V β Λ hfr g`. Take `⟨Λ₁, hle, hfg, heq⟩` from `exists_fg_sub hfr`. Establish `hfr₁ : Formalism.L2.DIV.IsFrame β Λ₁` using `fun x => by`. Rewrite using `[heq]`. Conclude with `hfr x`.

Rewrite using `[finE_mem_St_iff_of_fg V β Λ₁ hfr₁ hfg g]`. Establish `hL : ∀ v, GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ₁ v = GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v` using `fun v => by`. Unfold `GlobalTheory.AdelicU.stabLoc`. Rewrite using `[latLoc_eq hle hfg heq v]`. Simplify using `only [hL]`.
-/
theorem finE_mem_St_iff_stabLoc : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.L2.DIV.IsFrame β Λ → ∀ g : GA D V, Lev.finE V g ∈ Formalism.L2.DIV.St β ↔ ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := by
  intro D V β Λ hfr g
  obtain ⟨Λ₁, hle, hfg, heq⟩ := exists_fg_sub hfr
  have hfr₁ : Formalism.L2.DIV.IsFrame β Λ₁ := fun x => by
    rw [heq]; exact hfr x
  rw [finE_mem_St_iff_of_fg V β Λ₁ hfr₁ hfg g]
  have hL : ∀ v, GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ₁ v = GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := fun v => by
    unfold GlobalTheory.AdelicU.stabLoc
    rw [latLoc_eq hle hfg heq v]
  simp only [hL]

end GlobalTheory.ChainOnto.LStab
