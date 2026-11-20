import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CvBasic

open MeasureTheory
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.L1

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨ha, ha'⟩`. Consider the case `succ k ih`. Establish `h` using `cvBasic G μ a (cvPow μ a k) a ha ha' ih.1 ih.2 ha ha'`. Conclude with `⟨h.1, h.2.1⟩`.
-/
private theorem asx_cvPow {a : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (k : ℕ) :
    Continuous (cvPow μ a k) ∧ HasCompactSupport (cvPow μ a k) := by
  induction k with
  | zero => exact ⟨ha, ha'⟩
  | succ k ih =>
    have h := cvBasic G μ a (cvPow μ a k) a ha ha' ih.1 ih.2 ha ha'
    exact ⟨h.1, h.2.1⟩

/- English proof (translation)
Use `⟨by fun_prop, ?_⟩` and prove the remaining obligations. Establish `h : HasCompactSupport (fun x => b x⁻¹)` using `hb'.comp_homeomorph (Homeomorph.inv G)`. Conclude with `h.comp_left (g := fun z : ℂ => conj z) (map_zero _)`.
-/
private theorem asx_star {b : G → ℂ} (hb : Continuous b) (hb' : HasCompactSupport b) :
    Continuous (fun x => conj (b x⁻¹)) ∧ HasCompactSupport (fun x => conj (b x⁻¹)) := by
  refine ⟨by fun_prop, ?_⟩
  have h : HasCompactSupport (fun x => b x⁻¹) := hb'.comp_homeomorph (Homeomorph.inv G)
  exact h.comp_left (g := fun z : ℂ => conj z) (map_zero _)

end

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 in
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ m D n νF _ b hs hf hn`. Take `⟨-, -, -, -, -, -, hHaar, hTens⟩` from `archBasic F E σ m D n`. Establish `hb : Continuous (fun g => b g)` using `map_continuous b`. Establish `hb' : HasCompactSupport (fun g => b g)` using `b.hasCompactSupport`. Take `⟨h1, h2⟩` from `asx_star hb hb'`.

Establish `hc` using `cvBasic _ νF (fun g => b g) (fun x => conj (b x⁻¹)) (fun g => b g) hb hb' h1 h2 hb hb'`. Set `a : TI F n` to `⟨⟨cv νF (fun g => b g) (fun x => conj (b x⁻¹)), hc.1⟩, hc.2.1⟩`. Take `⟨aE, haE⟩` from `hTens fun _ => a`. Take `⟨h3, h4⟩` from `asx_cvPow νF (a := fun g => a g) (map_continuous a) a.hasCompactSupport m`. Set `aF : TI F n` to `⟨⟨cvPow νF (fun g => a g) m, h3⟩, h4⟩`.

Conclude with `⟨_, hHaar νF, a, aE, aF, { meas := rfl, smooth := hs, fin := hf, norm := hn, sq := fun _ => rfl, tens := haE, pow := fun _ => rfl }⟩`.
-/
theorem UpperTheory.ConvolutionTheory.L1.archPositionEx :
    UpperTheory.ConvolutionTheory.L1.ArchSlotEx := by
  intro F E _ _ _ _ _ σ m D n νF _ b hs hf hn
  obtain ⟨-, -, -, -, -, -, hHaar, hTens⟩ := archBasic F E σ m D n
  have hb : Continuous (fun g => b g) := map_continuous b
  have hb' : HasCompactSupport (fun g => b g) := b.hasCompactSupport
  obtain ⟨h1, h2⟩ := asx_star hb hb'
  have hc := cvBasic _ νF (fun g => b g) (fun x => conj (b x⁻¹)) (fun g => b g) hb hb' h1 h2 hb hb'
  let a : TI F n := ⟨⟨cv νF (fun g => b g) (fun x => conj (b x⁻¹)), hc.1⟩, hc.2.1⟩
  obtain ⟨aE, haE⟩ := hTens fun _ => a
  obtain ⟨h3, h4⟩ := asx_cvPow νF (a := fun g => a g) (map_continuous a) a.hasCompactSupport m
  let aF : TI F n := ⟨⟨cvPow νF (fun g => a g) m, h3⟩, h4⟩
  exact ⟨_, hHaar νF, a, aE, aF,
    { meas := rfl, smooth := hs, fin := hf, norm := hn, sq := fun _ => rfl, tens := haE, pow := fun _ => rfl }⟩
