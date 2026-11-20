import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.DsumCoh

variable {K : Type} [Field K] {I : Type 1} [DecidableEq I] (E : I → Cx.{1} K)

def inj (i : I) : Cx.Hom (E i) (Dsum E) (RingHom.id K) where
  f n := DirectSum.lof K I (fun i => (E i).X n) i
  comm n x := by
    change DirectSum.lmap (fun i => (E i).d n) (DirectSum.lof K I (fun i => (E i).X n) i x) = _
    rw [DirectSum.lmap_lof]
    rfl

def prj (i : I) : Cx.Hom (Dsum E) (E i) (RingHom.id K) where
  f n := DirectSum.component K I (fun i => (E i).X n) i
  comm n x := by
    change (E i).d n (DirectSum.component K I (fun i => (E i).X n) i x) =
      DirectSum.component K I (fun i => (E i).X (n + 1)) i (DirectSum.lmap (fun i => (E i).d n) x)
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      rw [← DirectSum.lof_eq_of K, DirectSum.lmap_lof]
      by_cases h : j = i
      · subst h
        simp only [DirectSum.component.lof_self]
      · rw [DirectSum.component.of, DirectSum.component.of, dif_neg h, dif_neg h, map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]

def toH (n : ℕ) : (⨁ i, (E i).H n) →ₗ[K] (Dsum E).H n :=
  DirectSum.toModule K I _ fun i => (inj E i).mapH n

/- English proof (translation)
Establish `hcl : ∀ (x y : (E i).X n) (hx : (E i).d n x = 0) (hy : (E i).d n y = 0), x = y → (E i).cls x hx = (E i).cls y hy`. Introduce and unpack `x _ _ _ rfl`. Both sides reduce to the same expression. Proceed by induction on `y using DirectSum.induction_on with`. Consider the case `zero => simp only [map_zero]`.

Consider the case `of j z`. Take `⟨a, ha, rfl⟩` from `CrystallineSemistableComparison.CechClassBoundaries.clsSurj z`. Establish `h1 : (Dsum E).d n ((inj E j).f n a) = 0` using `CrystallineSemistableComparison.CechClassBoundaries.cyc (inj E j) a ha`. Rewrite using `[← DirectSum.lof_eq_of K, toH, DirectSum.toModule_lof, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (inj E j) a ha h1, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (prj E i) _ h1 (CrystallineSemistableComparison.CechClassBoundaries.cyc (prj E i) …`. Distinguish the cases in `hji : j = i`.

Substitute `hji` using the available equality. Rewrite using `[DirectSum.component.lof_self]`. Conclude with `hcl _ _ _ _ (DirectSum.component.lof_self K _ _)`. Rewrite using `[DirectSum.component.of, dif_neg hji]`. Rewrite using `[← CrystallineSemistableComparison.CechClassBoundaries.cls_zero' (K := E i) (n := n) (map_zero _)]`.

Use `hcl _ _ _ _ ?_` and prove the remaining obligations. Use `show DirectSum.component K I (fun i ↦ (E i).X n) i (DirectSum.lof K I (fun i ↦ (E i).X n) j a) = 0`. Rewrite using `[DirectSum.component.of, dif_neg hji]`. Consider the case `add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]`.
-/
theorem prj_toH (n : ℕ) (i : I) (y : ⨁ i, (E i).H n) :
    (prj E i).mapH n (toH E n y) = DirectSum.component K I (fun i => (E i).H n) i y := by
  have hcl : ∀ (x y : (E i).X n) (hx : (E i).d n x = 0) (hy : (E i).d n y = 0), x = y →
      (E i).cls x hx = (E i).cls y hy := by
    rintro x _ _ _ rfl
    rfl
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of j z =>
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj z
    have h1 : (Dsum E).d n ((inj E j).f n a) = 0 := CrystallineSemistableComparison.CechClassBoundaries.cyc (inj E j) a ha
    rw [← DirectSum.lof_eq_of K, toH, DirectSum.toModule_lof, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (inj E j) a ha h1,
      CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (prj E i) _ h1 (CrystallineSemistableComparison.CechClassBoundaries.cyc (prj E i) _ h1)]
    by_cases hji : j = i
    · subst hji
      rw [DirectSum.component.lof_self]
      exact hcl _ _ _ _ (DirectSum.component.lof_self K _ _)
    · rw [DirectSum.component.of, dif_neg hji]
      rw [← CrystallineSemistableComparison.CechClassBoundaries.cls_zero' (K := E i) (n := n) (map_zero _)]
      refine hcl _ _ _ _ ?_
      show DirectSum.component K I (fun i ↦ (E i).X n) i (DirectSum.lof K I (fun i ↦ (E i).X n) j a) = 0
      rw [DirectSum.component.of, dif_neg hji]
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/- English proof (translation)
Use `(injective_iff_map_eq_zero (toH E n)).2 fun y hy ↦ ?_` and prove the remaining obligations. Use `DirectSum.ext fun i ↦ ?_` and prove the remaining obligations. Establish `h` using `prj_toH E n i y`. Rewrite `h` using `[hy, map_zero]`. Rewrite using `[DirectSum.apply_eq_component K, ← h]`.

Both sides reduce to the same expression.
-/
theorem toH_injective (n : ℕ) : Function.Injective (toH E n) := by
  refine (injective_iff_map_eq_zero (toH E n)).2 fun y hy ↦ ?_
  refine DirectSum.ext fun i ↦ ?_
  have h := prj_toH E n i y
  rw [hy, map_zero] at h
  rw [DirectSum.apply_eq_component K, ← h]
  rfl

/- English proof (translation)
Introduce `z`. Take `⟨x, hx, rfl⟩` from `CrystallineSemistableComparison.CechClassBoundaries.clsSurj z`. Establish `hc : ∀ i, (E i).d n ((prj E i).f n x) = 0` using `fun i ↦ CrystallineSemistableComparison.CechClassBoundaries.cyc (prj E i) x hx`. Establish `hci : ∀ i, (Dsum E).d n ((inj E i).f n ((prj E i).f n x)) = 0` using `fun i ↦ CrystallineSemistableComparison.CechClassBoundaries.cyc (inj E i) _ (hc i)`. Establish `hsum : ∀ S : Finset I, ∀ h : (Dsum E).d n (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) = 0, (Dsum E).cls (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) h = ∑ i ∈ S, (Dsum E).cls ((inj E i).f n ((prj E i).f n x)) (hci i)`.

Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `h`. Simplify using `only [Finset.sum_empty]`.

Conclude with `CrystallineSemistableComparison.CechClassBoundaries.cls_zero' h`. Consider the case `insert j S hj ih`. Introduce `h`. Establish `hS : (Dsum E).d n (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) = 0`. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_eq_zero fun i _ ↦ hci i`. Simplify using `only [Finset.sum_insert hj]`. Rewrite using `[CrystallineSemistableComparison.CechClassBoundaries.cls_add _ _ (hci j) hS, ih hS]`. Establish `hx_eq : ∑ i ∈ DFinsupp.support x, (inj E i).f n ((prj E i).f n x) = x` using `by conv_rhs => rw [← DirectSum.sum_support_of x]`. Both sides reduce to the same expression.

Use `⟨∑ i ∈ DFinsupp.support x, DirectSum.lof K I (fun i ↦ (E i).H n) i ((E i).cls _ (hc i)), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Simplify using `only [toH, DirectSum.toModule_lof]`. Establish `hx' : (Dsum E).d n (∑ i ∈ DFinsupp.support x, (inj E i).f n ((prj E i).f n x)) = 0`. Rewrite using `[hx_eq]`.

Conclude with `hx`. Rewrite using `[Finset.sum_congr rfl fun i _ ↦ CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (inj E i) _ (hc i) (hci i), ← hsum _ hx']`. Conclude with `(CrystallineSemistableComparison.CechClassBoundaries.cls_eq _ _ _ _).2 (by rw [hx_eq, sub_self]; exact zero_mem _)`.
-/
theorem toH_surjective (n : ℕ) : Function.Surjective (toH E n) := by
  classical
  intro z
  obtain ⟨x, hx, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj z
  have hc : ∀ i, (E i).d n ((prj E i).f n x) = 0 := fun i ↦ CrystallineSemistableComparison.CechClassBoundaries.cyc (prj E i) x hx
  have hci : ∀ i, (Dsum E).d n ((inj E i).f n ((prj E i).f n x)) = 0 := fun i ↦ CrystallineSemistableComparison.CechClassBoundaries.cyc (inj E i) _ (hc i)
  have hsum : ∀ S : Finset I, ∀ h : (Dsum E).d n (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) = 0,
      (Dsum E).cls (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) h =
        ∑ i ∈ S, (Dsum E).cls ((inj E i).f n ((prj E i).f n x)) (hci i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro h
      simp only [Finset.sum_empty]
      exact CrystallineSemistableComparison.CechClassBoundaries.cls_zero' h
    | insert j S hj ih =>
      intro h
      have hS : (Dsum E).d n (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) = 0 := by
        rw [map_sum]
        exact Finset.sum_eq_zero fun i _ ↦ hci i
      simp only [Finset.sum_insert hj]
      rw [CrystallineSemistableComparison.CechClassBoundaries.cls_add _ _ (hci j) hS, ih hS]
  have hx_eq : ∑ i ∈ DFinsupp.support x, (inj E i).f n ((prj E i).f n x) = x := by
    conv_rhs => rw [← DirectSum.sum_support_of x]
    rfl
  refine ⟨∑ i ∈ DFinsupp.support x, DirectSum.lof K I (fun i ↦ (E i).H n) i ((E i).cls _ (hc i)), ?_⟩
  rw [map_sum]
  simp only [toH, DirectSum.toModule_lof]
  have hx' : (Dsum E).d n (∑ i ∈ DFinsupp.support x, (inj E i).f n ((prj E i).f n x)) = 0 := by
    rw [hx_eq]
    exact hx
  rw [Finset.sum_congr rfl fun i _ ↦ CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (inj E i) _ (hc i) (hci i), ← hsum _ hx']
  exact (CrystallineSemistableComparison.CechClassBoundaries.cls_eq _ _ _ _).2 (by rw [hx_eq, sub_self]; exact zero_mem _)

end GlobalTheory.CompanionTheory.KunGlue.DsumCoh

/- English proof (translation)
Introduce `K _ I _ E n`. Use `⟨LinearEquiv.ofBijective (DsumCoh.toH E n) ⟨DsumCoh.toH_injective E n, DsumCoh.toH_surjective E n⟩, fun i x hx hx' ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[LinearEquiv.ofBijective_apply, DsumCoh.toH, DirectSum.toModule_lof]`. Conclude with `CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (DsumCoh.inj E i) x hx hx'`.
-/
theorem GlobalTheory.CompanionTheory.KunGlue.dsum_coh : ∀ {K : Type} [Field K] {I : Type 1} [DecidableEq I] (E : I → Cx.{1} K) (n : ℕ),
    ∃ e : (⨁ i, (E i).H n) ≃ₗ[K] (Dsum E).H n, ∀ (i : I) (x : (E i).X n) (hx : (E i).d n x = 0)
      (hx' : (Dsum E).d n (DirectSum.lof K I (fun i => (E i).X n) i x) = 0),
      e (DirectSum.lof K I (fun i => (E i).H n) i ((E i).cls x hx)) =
        (Dsum E).cls (DirectSum.lof K I (fun i => (E i).X n) i x) hx' := by
  intro K _ I _ E n
  refine ⟨LinearEquiv.ofBijective (DsumCoh.toH E n) ⟨DsumCoh.toH_injective E n, DsumCoh.toH_surjective E n⟩,
    fun i x hx hx' ↦ ?_⟩
  rw [LinearEquiv.ofBijective_apply, DsumCoh.toH, DirectSum.toModule_lof]
  exact CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (DsumCoh.inj E i) x hx hx'
