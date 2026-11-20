import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesLocalSuppIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LocAgree

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit

variable {D : D7}

/- English proof (translation)
The claim follows from `le_antisymm (latV_mono S L fun w => (h w).1) (latV_mono S L fun w => (h w).2)`.
-/
theorem latV_congr (S : HSp D) (L : Lat S) {P P' : Pl D → Prop} (h : ∀ w, P w ↔ P' w) :
    latV S L P = latV S L P' :=
  le_antisymm (latV_mono S L fun w => (h w).1) (latV_mono S L fun w => (h w).2)

/- English proof (translation)
Rewrite using `[latV, latMul, AddSubgroup.closure_le]`. Introduce and unpack `y ⟨α, hα, hsupp, a, ha, x, hx, rfl⟩`. Rewrite `ha` using `[Set.mem_singleton_iff]`. Substitute `ha` using the available equality. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises.

Use `⟨((d : D.host.F))⁻¹ • α, ?_, ?_, 1, rfl, d • x, hLM x hx, ?_⟩` and prove the remaining obligations. Introduce `w`. Rewrite using `[map_smul]`. Distinguish the cases in `hw : R w`. Establish `hval : Valued.v (algebraMap D.host.F (w.adicCompletion D.host.F) (d : D.host.F)) = 1`.

Establish `h1` using `(w.valuation_eq_one_iff_notMem (K := D.host.F)).mpr (hR w hw)`. Establish `h2` using `w.valuedAdicCompletion_eq_valuation' (K := D.host.F) ((d : D.host.F))`. Establish `h4 : (((d : 𝓞 D.host.F)) : D.host.F) = ((d : D.host.F))` using `map_intCast (algebraMap (𝓞 D.host.F) D.host.F) _`. Conclude with `h2.trans (h4 ▸ h1)`. Establish `hαw` using `hα w`.

Rewrite `hαw`, the goal using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Rewrite using `[Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]`. Conclude with `hαw`. Rewrite using `[hsupp w hw, smul_zero]`. Conclude with `zero_mem _`.

Introduce `w hw`. Rewrite using `[map_smul, hsupp w hw, smul_zero]`. Use function extensionality and compare the values at `i`. Conclude with `pairA_tmul_int_gen d hd α (x i)`.
-/
theorem latV_le_of_int_smul_on (S : HSp D) (L M : Lat S) (d : ℤ) (hd : d ≠ 0)
    (hLM : ∀ x ∈ L, d • x ∈ M) (R : Pl D → Prop) (hR : ∀ v, R v → ((d : 𝓞 D.host.F)) ∉ v.asIdeal) :
    latV S L R ≤ latV S M R := by
  rw [latV, latMul, AddSubgroup.closure_le]
  rintro y ⟨α, hα, hsupp, a, ha, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at ha
  subst ha
  apply AddSubgroup.subset_closure
  refine ⟨((d : D.host.F))⁻¹ • α, ?_, ?_, 1, rfl, d • x, hLM x hx, ?_⟩
  · intro w
    rw [map_smul]
    by_cases hw : R w
    · have hval : Valued.v (algebraMap D.host.F (w.adicCompletion D.host.F) (d : D.host.F)) = 1 := by
        have h1 := (w.valuation_eq_one_iff_notMem (K := D.host.F)).mpr (hR w hw)
        have h2 := w.valuedAdicCompletion_eq_valuation' (K := D.host.F) ((d : D.host.F))
        have h4 : (((d : 𝓞 D.host.F)) : D.host.F) = ((d : D.host.F)) :=
          map_intCast (algebraMap (𝓞 D.host.F) D.host.F) _
        exact h2.trans (h4 ▸ h1)
      have hαw := hα w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hαw ⊢
      rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]
      exact hαw
    · rw [hsupp w hw, smul_zero]
      exact zero_mem _
  · intro w hw
    rw [map_smul, hsupp w hw, smul_zero]
  · funext i
    exact pairA_tmul_int_gen d hd α (x i)

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Conclude with `latV_le_of_int_smul_on S L N d hd hLN _ fun v hv => absurd hv.2 (Finset.notMem_empty v)`. Consider the case `insert a T' ha ih`. Introduce `z hz`.

Establish `hs` using `GlobalTheory.FinPlLoc.latV_idAt hz`. Take `⟨h1, h2⟩` from `(mem_latV_iff_parts S L _ {a} hs).1 hz`. Rewrite using `[mem_latV_iff_parts S N _ {a} hs]`. Prove the components needed by the constructor for the conclusion. Distinguish the cases in `hPa : P a`.

Establish `hiff : ∀ w, ((P w ∧ w ∈ insert a T') ∧ w ∈ ({a} : Finset (Pl D))) ↔ w = a`. Introduce `w`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.2`.

Introduce and unpack `rfl`. Conclude with `⟨⟨hPa, Or.inl rfl⟩, rfl⟩`. Rewrite `h1` using `[latV_congr S L hiff, hP a hPa]`. Rewrite using `[latV_congr S N hiff]`. Conclude with `h1`.

Use `latV_le_of_int_smul_on S L N d hd hLN _ (fun v hv => ?_) h1` and prove the remaining obligations. Conclude with `absurd (Finset.mem_singleton.1 hv.2 ▸ hv.1.1) hPa`. Establish `hiff : ∀ w, ((P w ∧ w ∈ insert a T') ∧ w ∉ ({a} : Finset (Pl D))) ↔ (P w ∧ w ∈ T')`. Introduce `w`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hw, h | h⟩, hne⟩`. Conclude with `absurd h hne`. Conclude with `⟨hw, h⟩`. Introduce and unpack `⟨hw, h⟩`.

Conclude with `⟨⟨hw, Or.inr h⟩, fun e => ha (e ▸ h)⟩`. Rewrite `h2` using `[latV_congr S L hiff]`. Rewrite using `[latV_congr S N hiff]`. Conclude with `ih h2`.
-/
theorem latV_le_finite (S : HSp D) (L N : Lat S) (d : ℤ) (hd : d ≠ 0) (hLN : ∀ x ∈ L, d • x ∈ N)
    (P : Pl D → Prop) (hP : ∀ w, P w → latV S L (· = w) = latV S N (· = w)) (T : Finset (Pl D)) :
    latV S L (fun p => P p ∧ p ∈ T) ≤ latV S N (fun p => P p ∧ p ∈ T) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact latV_le_of_int_smul_on S L N d hd hLN _ fun v hv => absurd hv.2 (Finset.notMem_empty v)
  | insert a T' ha ih =>
    intro z hz
    have hs := GlobalTheory.FinPlLoc.latV_idAt hz
    obtain ⟨h1, h2⟩ := (mem_latV_iff_parts S L _ {a} hs).1 hz
    rw [mem_latV_iff_parts S N _ {a} hs]
    constructor
    · by_cases hPa : P a
      · have hiff : ∀ w, ((P w ∧ w ∈ insert a T') ∧ w ∈ ({a} : Finset (Pl D))) ↔ w = a := by
          intro w
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · exact fun h => h.2
          · rintro rfl; exact ⟨⟨hPa, Or.inl rfl⟩, rfl⟩
        rw [latV_congr S L hiff, hP a hPa] at h1
        rw [latV_congr S N hiff]
        exact h1
      · refine latV_le_of_int_smul_on S L N d hd hLN _ (fun v hv => ?_) h1
        exact absurd (Finset.mem_singleton.1 hv.2 ▸ hv.1.1) hPa
    · have hiff : ∀ w, ((P w ∧ w ∈ insert a T') ∧ w ∉ ({a} : Finset (Pl D))) ↔ (P w ∧ w ∈ T') := by
        intro w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hw, h | h⟩, hne⟩
          · exact absurd h hne
          · exact ⟨hw, h⟩
        · rintro ⟨hw, h⟩
          exact ⟨⟨hw, Or.inr h⟩, fun e => ha (e ▸ h)⟩
      rw [latV_congr S L hiff] at h2
      rw [latV_congr S N hiff]
      exact ih h2

/- English proof (translation)
Use `set T := (finite_places_int (D := D) d hd).toFinset`. Introduce `y hy`. Establish `hs` using `GlobalTheory.FinPlLoc.latV_idAt hy`. Take `⟨h1, h2⟩` from `(mem_latV_iff_parts S L P T hs).1 hy`. Rewrite using `[mem_latV_iff_parts S N P T hs]`.

Use `⟨latV_le_finite S L N d hd hLN P hP T h1, latV_le_of_int_smul_on S L N d hd hLN _ (fun v hv => ?_) h2⟩` and prove the remaining obligations. Introduce `hmem`. Conclude with `hv.2 ((Set.Finite.mem_toFinset _).2 hmem)`.
-/
theorem latV_le_of_local (S : HSp D) (L N : Lat S) (d : ℤ) (hd : d ≠ 0) (hLN : ∀ x ∈ L, d • x ∈ N)
    (P : Pl D → Prop) (hP : ∀ w, P w → latV S L (· = w) = latV S N (· = w)) : latV S L P ≤ latV S N P := by
  classical
  set T := (finite_places_int (D := D) d hd).toFinset
  intro y hy
  have hs := GlobalTheory.FinPlLoc.latV_idAt hy
  obtain ⟨h1, h2⟩ := (mem_latV_iff_parts S L P T hs).1 hy
  rw [mem_latV_iff_parts S N P T hs]
  refine ⟨latV_le_finite S L N d hd hLN P hP T h1, latV_le_of_int_smul_on S L N d hd hLN _ (fun v hv => ?_) h2⟩
  intro hmem
  exact hv.2 ((Set.Finite.mem_toFinset _).2 hmem)

/- English proof (translation)
Introduce `D S L N P hL hN hP`. Take `⟨d₁, hd₁, h₁⟩` from `exists_int_smul_le L N hL.fg hN.span_eq_top`. Take `⟨d₂, hd₂, h₂⟩` from `exists_int_smul_le N L hN.fg hL.span_eq_top`. Conclude with `le_antisymm (latV_le_of_local S L N d₁ hd₁ h₁ P hP) (latV_le_of_local S N L d₂ hd₂ h₂ P fun w hw => (hP w hw).symm)`.
-/
theorem latV_eq_of_local : ∀ {D : D7} (S : HSp D) (L N : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop),
    Submodule.IsLattice D.host.E L → Submodule.IsLattice D.host.E N →
    (∀ w, P w → GlobalTheory.FinPl.latV S L (· = w) = GlobalTheory.FinPl.latV S N (· = w)) →
    GlobalTheory.FinPl.latV S L P = GlobalTheory.FinPl.latV S N P := by
  intro D S L N P hL hN hP
  obtain ⟨d₁, hd₁, h₁⟩ := exists_int_smul_le L N hL.fg hN.span_eq_top
  obtain ⟨d₂, hd₂, h₂⟩ := exists_int_smul_le N L hN.fg hL.span_eq_top
  exact le_antisymm (latV_le_of_local S L N d₁ hd₁ h₁ P hP)
    (latV_le_of_local S N L d₂ hd₂ h₂ P fun w hw => (hP w hw).symm)

end GlobalTheory.FinPl.LocAgree

end
