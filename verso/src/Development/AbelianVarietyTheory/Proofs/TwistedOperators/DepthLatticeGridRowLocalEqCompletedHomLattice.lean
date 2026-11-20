import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOConstMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelStepVectorEqHeisenbergCombinationVacuum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.RowLoc

variable {D : D7}

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Simplify using `[negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]`.
-/
theorem gen_negSp (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * (negSp S).gram k j) : WO (negSp S) T) =
      -(Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) := by
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hu`. Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩` from `hw`.

Rewrite using `[gen_negSp]`. Conclude with `neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩)`. Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `neg x _ hx => exact neg_mem hx`.

Introduce `hu`. Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩` from `hw`. Rewrite using `[← neg_neg (Matrix.of _), ← gen_negSp]`.

Conclude with `neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩)`. Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `neg x _ hx => exact neg_mem hx`.
-/
theorem mem_latO_negSp {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} {u : WO S T} : u ∈ latO (negSp S) T LS LT P ↔ u ∈ latO S T LS LT P := by
  constructor
  · intro hu
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
      rw [gen_negSp]
      exact neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro hu
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
      rw [← neg_neg (Matrix.of _), ← gen_negSp]
      exact neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx

/- English proof (translation)
Introduce `D _ T L μ0 _ sc G W M _ i _ v hv u hu`. Establish `hoff : ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u = 0`. Introduce `e he`. Establish `he'` using `GlobalTheory.StepComb.idemSum_mem_idAt he`. Establish `hev : e ∈ idOff D (· = v)`.

Rewrite using `[idOff, Ideal.mem_iInf]`. Introduce and unpack `⟨w, rfl⟩`. Rewrite `he'` using `[idAt, Ideal.mem_inf, Ideal.mem_iInf]`. Use `he'.2 ⟨w, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨PP, hPP, hw⟩`.

Simplify using `only [Places.W0, Finset.mem_image] at hPP`. Take `⟨s, hs, rfl⟩` from `hPP`. Conclude with `hv (by rw [hw, G.pl.under_w hs]; exact hs)`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, smul_eq_mul, mul_comm, Matrix.zero_apply]`.

Conclude with `GlobalTheory.FinPl.FlatUnitPf.idAt_mul_idOff _ _ _ (hu a b) hev`. Establish `k1 : u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) ↔ u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True)` using `mem_latO_negSp`. Establish `k2 : u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) ↔ u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)` using `GlobalTheory.AscFinWit.mem_latO_at (LS := G.Λ (.grid (i + 1) 0)) (LT := G.Λ (.grid i 0)) hu`. Conclude with `⟨fun h => k2.1 (k1.1 h.1), fun h => ⟨k1.2 (k2.2 h), fun e he => by rw [hoff e he]; exact zero_mem _⟩⟩`.
-/
theorem latRow_at : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v ∉ G.pl.S0, ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)),
    MxAt (· = v) u → (u ∈ latRow G i ↔ u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)) := by
  intro D _ T L μ0 _ sc G W M _ i _ v hv u hu
  have hoff : ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u = 0 := by
    intro e he
    have he' := GlobalTheory.StepComb.idemSum_mem_idAt he
    have hev : e ∈ idOff D (· = v) := by
      rw [idOff, Ideal.mem_iInf]
      rintro ⟨w, rfl⟩
      rw [idAt, Ideal.mem_inf, Ideal.mem_iInf] at he'
      refine he'.2 ⟨w, ?_⟩
      rintro ⟨PP, hPP, hw⟩
      classical
      simp only [Places.W0, Finset.mem_image] at hPP
      obtain ⟨s, hs, rfl⟩ := hPP
      exact hv (by rw [hw, G.pl.under_w hs]; exact hs)
    refine Matrix.ext fun a b => ?_
    rw [Matrix.smul_apply, smul_eq_mul, mul_comm, Matrix.zero_apply]
    exact GlobalTheory.FinPl.FlatUnitPf.idAt_mul_idOff _ _ _ (hu a b) hev
  have k1 : u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) ↔
      u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) := mem_latO_negSp
  have k2 : u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) ↔
      u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v) :=
    GlobalTheory.AscFinWit.mem_latO_at (LS := G.Λ (.grid (i + 1) 0)) (LT := G.Λ (.grid i 0)) hu
  exact ⟨fun h => k2.1 (k1.1 h.1), fun h => ⟨k1.2 (k2.2 h), fun e he => by rw [hoff e he]; exact zero_mem _⟩⟩

end GlobalTheory.RowLoc
