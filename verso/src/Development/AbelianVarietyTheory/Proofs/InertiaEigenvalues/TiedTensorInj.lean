import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLinearDisjointStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaxUnramifiedOfCrystallineRatioStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvFilD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisExtra
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.LocTensor

/- English proof (translation)
Use `letI : Field D := hD.toField`. Establish `hcl : ∀ y : D, y ∈ Subring.closure (Set.range ι) ↔ ∃ a, ι a = y`. Introduce `y`. Establish `: Subring.closure (Set.range ι) = ι.range`. Rewrite using `[← RingHom.coe_range, Subring.closure_eq]`.

Rewrite using `[this]`. Both sides reduce to the same expression. Establish `key` using `GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent k Ω D o (Subfield.closure (Set.range ι)) (by`. Introduce `y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Take `⟨u, hu, v, hv, huv⟩` from `Subfield.mem_closure_iff.1 hy`. Take `⟨a, rfl⟩` from `(hcl u).1 hu`. Take `⟨c, rfl⟩` from `(hcl v).1 hv`. Distinguish the cases in `hc : c = 0`.

Substitute `hc` using the available equality. Rewrite `huv` using `[map_zero, div_zero]`. Establish `: y = 0` using `o.injective (by rw [map_zero]; exact huv.symm)`. Rewrite using `[this]`. Conclude with `zero_mem _`.

Establish `hc' : ι c ≠ 0` using `fun h => hc (hι (by rw [h, map_zero]))`. Use `hfrac a c y hc ?_` and prove the remaining obligations. Rewrite using `[← huv, div_mul_cancel₀ _ hc']`. Introduce and unpack `⟨c, rfl⟩`. Take `⟨a, ha⟩` from `hk c`.

Conclude with `Subfield.subset_closure ⟨a, ha⟩) m x hx (fun i => ι (b i))`. Use the proof step `(fun i => Subfield.subset_closure ⟨b i, rfl⟩) hb`. Introduce `i`. Conclude with `hι (by rw [map_zero]; exact key i)`.
-/
theorem indep_of_frac {k Ω B D : Type} [Field k] [Field Ω] [CommRing B] [CommRing D] [Algebra k Ω]
    [IsGalois k Ω] (hD : IsField D) (o : Ω →+* D) (ι : B →+* D) (hι : Function.Injective ι)
    (hk : ∀ c : k, ∃ a : B, ι a = o (algebraMap k Ω c))
    (hfrac : ∀ (a b : B) (x : Ω), b ≠ 0 → ι a = o x * ι b → x ∈ (algebraMap k Ω).range)
    (m : ℕ) (x : Fin m → Ω) (hx : LinearIndependent k x) (b : Fin m → B)
    (hb : ∑ i, o (x i) * ι (b i) = 0) : ∀ i, b i = 0 := by
  letI : Field D := hD.toField
  have hcl : ∀ y : D, y ∈ Subring.closure (Set.range ι) ↔ ∃ a, ι a = y := by
    intro y
    have : Subring.closure (Set.range ι) = ι.range := by
      rw [← RingHom.coe_range, Subring.closure_eq]
    rw [this]; rfl
  have key := GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent k Ω D o (Subfield.closure (Set.range ι)) (by
    intro y
    constructor
    · intro hy
      obtain ⟨u, hu, v, hv, huv⟩ := Subfield.mem_closure_iff.1 hy
      obtain ⟨a, rfl⟩ := (hcl u).1 hu
      obtain ⟨c, rfl⟩ := (hcl v).1 hv
      by_cases hc : c = 0
      · subst hc
        rw [map_zero, div_zero] at huv
        have : y = 0 := o.injective (by rw [map_zero]; exact huv.symm)
        rw [this]; exact zero_mem _
      · have hc' : ι c ≠ 0 := fun h => hc (hι (by rw [h, map_zero]))
        refine hfrac a c y hc ?_
        rw [← huv, div_mul_cancel₀ _ hc']
    · rintro ⟨c, rfl⟩
      obtain ⟨a, ha⟩ := hk c
      exact Subfield.subset_closure ⟨a, ha⟩) m x hx (fun i => ι (b i))
    (fun i => Subfield.subset_closure ⟨b i, rfl⟩) hb
  intro i
  exact hι (by rw [map_zero]; exact key i)

/- English proof (translation)
Introduce `l _ P AI T m x hx b hb`. Take `⟨hD, -, hι, -⟩` from `GlobalTheory.Per.TiedField.tied_field l P AI T`. Use `haveI : IsGalois ℚ_[l] (Om l) := inferInstance`. Use `haveI : IsGalois ↥(MaximalUnramifiedExtension l) (Om l) := inferInstance`. Use `indep_of_frac (k := ↥(MaximalUnramifiedExtension l)) hD (algebraMap (Om l) P.R.BdR) (P.ιB : P.R.B →+* P.R.BdR) hι (fun c => ⟨algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c, GlobalTheory.LocIota.tied_ιB_algebraMap_Kur l P AI T c⟩) ?_ m x hx b hb` and prove the remaining obligations.

Introduce `a c y hc h`. Conclude with `⟨⟨y, GlobalTheory.T.mem_maxUnramified_of_crystallineRatio l P AI T a c y hc h⟩, rfl⟩`.
-/
theorem tied_tensor_inj : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (m : ℕ) (x : Fin m → Om l), LinearIndependent ↥(MaximalUnramifiedExtension l) x → ∀ b : Fin m → P.R.B, ∑ i, algebraMap (Om l) P.R.BdR (x i) * P.ιB (b i) = 0 → ∀ i, b i = 0 := by
  intro l _ P AI T m x hx b hb
  obtain ⟨hD, -, hι, -⟩ := GlobalTheory.Per.TiedField.tied_field l P AI T
  haveI : IsGalois ℚ_[l] (Om l) := inferInstance
  haveI : IsGalois ↥(MaximalUnramifiedExtension l) (Om l) := inferInstance
  refine indep_of_frac (k := ↥(MaximalUnramifiedExtension l)) hD (algebraMap (Om l) P.R.BdR) (P.ιB : P.R.B →+* P.R.BdR) hι
    (fun c => ⟨algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c, GlobalTheory.LocIota.tied_ιB_algebraMap_Kur l P AI T c⟩) ?_ m x hx b hb
  intro a c y hc h
  exact ⟨⟨y, GlobalTheory.T.mem_maxUnramified_of_crystallineRatio l P AI T a c y hc h⟩, rfl⟩

end GlobalTheory.LocTensor
