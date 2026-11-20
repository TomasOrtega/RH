import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPrBPtMP
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnEvProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnEvPtP
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

/- English proof (translation)
Apply `TopologicalSpace.Opens.ext` to reduce the goal to its premises. Use extensionality with `x`. Use `⟨fun hx => Set.mem_iInter.1 hx 0, fun hx => Set.mem_iInter.2 fun k => ?_⟩` and prove the remaining obligations. Take `rfl : k = 0` from `Fin.fin_one_eq_zero k`. Conclude with `hx`.
-/
theorem mchart_zero (n : Fin 1 → ℕ) (c : ∀ k, Bk n k) :
    mchart c = (chart ℤ (n 0) (c 0) : (MP ℤ 0 n).Opens) := by
  apply TopologicalSpace.Opens.ext
  ext x
  refine ⟨fun hx => Set.mem_iInter.1 hx 0, fun hx => Set.mem_iInter.2 fun k => ?_⟩
  obtain rfl : k = 0 := Fin.fin_one_eq_zero k
  exact hx

/- English proof (translation)
Apply `TopologicalSpace.Opens.ext` to reduce the goal to its premises. Use extensionality with `x`. Use `⟨fun hx => ⟨Set.mem_iInter.1 hx 0, Set.mem_iInter.2 fun j => Set.mem_iInter.1 hx j.succ⟩, fun hx => Set.mem_iInter.2 fun k => ?_⟩` and prove the remaining obligations. Proceed by induction on `k using Fin.cases with`. Consider the case `zero => exact hx.1`.

Consider the case `succ j => exact Set.mem_iInter.1 hx.2 j`.
-/
theorem mchart_succ {m : ℕ} (n : Fin (m + 2) → ℕ) (c : ∀ k, Bk n k) :
    mchart c = (pullback.fst (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ chart ℤ (n 0) (c 0) ⊓
      pullback.snd (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ
        mchart (n := Fin.tail n) (fun j => c j.succ) : (MP ℤ (m + 1) n).Opens) := by
  apply TopologicalSpace.Opens.ext
  ext x
  refine ⟨fun hx => ⟨Set.mem_iInter.1 hx 0, Set.mem_iInter.2 fun j => Set.mem_iInter.1 hx j.succ⟩,
    fun hx => Set.mem_iInter.2 fun k => ?_⟩
  induction k using Fin.cases with
  | zero => exact hx.1
  | succ j => exact Set.mem_iInter.1 hx.2 j

/- English proof (translation)
The claim follows from `GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr _ _ _ _ _ 0`.
-/
theorem multiprojectivePoint_fst {m : ℕ} (n : Fin (m + 2) → ℕ) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) :
    (multiprojectivePoint c z).1 ≫ pullback.fst (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) =
      (ptP (n 0) (c 0) (fun i => z ⟨0, i⟩)).1 :=
  GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr _ _ _ _ _ 0

/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
theorem multiprojectivePoint_snd {m : ℕ} (n : Fin (m + 2) → ℕ) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) :
    (multiprojectivePoint c z).1 ≫ pullback.snd (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) =
      (multiprojectivePoint (n := Fin.tail n) (fun j => c j.succ) (fun p => z ⟨p.1.succ, p.2⟩)).1 :=
  pullback.lift_snd _ _ _

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `n c`. Establish `key : ∀ W : (MP ℤ 0 n).Opens, W = (chart ℤ (n 0) (c 0) : (MP ℤ 0 n).Opens) → IsAffineOpen W ∧ (∀ z ∈ {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0}, multiprojectivePoint c z ∈ ptsIn (mpStr ℤ 0 n) σ₀ W) ∧ ∀ a : Γ(MP ℤ 0 n, W), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ 0 n) σ₀ W a ∘ mul …`. Introduce and unpack `W rfl`.

Establish `hpt : ∀ z : (Σ k, Bk n k) → ℂ, multiprojectivePoint c z = ptP (n 0) (c 0) (fun i => z ⟨0, i⟩)` using `fun z => rfl`. Use `⟨isAffineOpen_chart ℤ (n 0) (c 0), fun z _ => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hpt]`. Conclude with `CxPts.ofHom_mem _ _ _`. Establish `hL : Differentiable ℂ (fun (z : (Σ k, Bk n k) → ℂ) (i : Fin (n 0 + 1)) => z ⟨0, i⟩)` using `differentiable_pi.2 fun i => differentiable_apply _`.

Conclude with `(GlobalTheory.CompanionTheory.MPSmooth.differentiableOn_ev_ptP (n 0) (c 0) a).comp hL.differentiableOn fun z hz => hz 0`. Conclude with `key _ (mchart_zero n c)`. Consider the case `succ m ih`. Introduce `n c`. Take `⟨hA, hM, hD⟩` from `ih (Fin.tail n) (fun j => c j.succ)`.

Establish `hL : Differentiable ℂ (fun (z : (Σ k, Bk n k) → ℂ) (p : Σ k, Bk (Fin.tail n) k) => z ⟨p.1.succ, p.2⟩)` using `differentiable_pi.2 fun p => differentiable_apply _`. Establish `hL0 : Differentiable ℂ (fun (z : (Σ k, Bk n k) → ℂ) (i : Fin (n 0 + 1)) => z ⟨0, i⟩)` using `differentiable_pi.2 fun i => differentiable_apply _`. Establish `hT : Set.MapsTo (fun (z : (Σ k, Bk n k) → ℂ) (p : Σ k, Bk (Fin.tail n) k) => z ⟨p.1.succ, p.2⟩) {z | ∀ k, z ⟨k, c k⟩ ≠ 0} {z : (Σ k, Bk (Fin.tail n) k) → ℂ | ∀ k, z ⟨k, c k.succ⟩ ≠ 0}` using `fun z hz k => hz k.succ`. Establish `main` using `GlobalTheory.CompanionTheory.Ar.ProdHolo.differentiableOn_ev_prod (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) σ₀ {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} (chart ℤ (n 0) (c 0)) (mchart (n := Fin.tail n) (fun j => c j.succ)) (isAffineOpen_chart ℤ (n 0) (c 0)) hA (fun z => pt …`. Establish `key : ∀ W : (MP ℤ (m + 1) n).Opens, W = (pullback.fst (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ chart ℤ (n 0) (c 0) ⊓ pullback.snd (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ mchart (n` using `Fin.tail n) (fun j => c j.succ) : (MP ℤ (m + 1) n).Opens) → IsAffineOpen W ∧ (∀ z ∈ {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0}, multiprojectivePoint c z ∈ ptsIn (mpStr ℤ (m + 1) n) σ₀ W) ∧ ∀ a : Γ(MP ℤ (m + 1) n, W), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ (m + 1) n) σ₀ W a ∘ mu …`.

Introduce and unpack `W rfl`. Conclude with `main`. Conclude with `key _ (mchart_succ n c)`.
-/
theorem multiprojective_chart_affine_holomorphic_points (m : ℕ) : ∀ (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k), IsAffineOpen (mchart c) ∧
    (∀ z ∈ {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0}, multiprojectivePoint c z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c)) ∧
    ∀ a : Γ(MP ℤ m n, mchart c), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) a ∘ multiprojectivePoint c)
      {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
  induction m with
  | zero =>
    intro n c
    have key : ∀ W : (MP ℤ 0 n).Opens, W = (chart ℤ (n 0) (c 0) : (MP ℤ 0 n).Opens) → IsAffineOpen W ∧
        (∀ z ∈ {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0}, multiprojectivePoint c z ∈ ptsIn (mpStr ℤ 0 n) σ₀ W) ∧
        ∀ a : Γ(MP ℤ 0 n, W), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ 0 n) σ₀ W a ∘ multiprojectivePoint c)
          {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      rintro W rfl
      have hpt : ∀ z : (Σ k, Bk n k) → ℂ, multiprojectivePoint c z = ptP (n 0) (c 0) (fun i => z ⟨0, i⟩) := fun z => rfl
      refine ⟨isAffineOpen_chart ℤ (n 0) (c 0), fun z _ => ?_, fun a => ?_⟩
      · rw [hpt]
        exact CxPts.ofHom_mem _ _ _
      · have hL : Differentiable ℂ (fun (z : (Σ k, Bk n k) → ℂ) (i : Fin (n 0 + 1)) => z ⟨0, i⟩) :=
          differentiable_pi.2 fun i => differentiable_apply _
        exact (GlobalTheory.CompanionTheory.MPSmooth.differentiableOn_ev_ptP (n 0) (c 0) a).comp hL.differentiableOn fun z hz => hz 0
    exact key _ (mchart_zero n c)
  | succ m ih =>
    intro n c
    obtain ⟨hA, hM, hD⟩ := ih (Fin.tail n) (fun j => c j.succ)
    have hL : Differentiable ℂ (fun (z : (Σ k, Bk n k) → ℂ) (p : Σ k, Bk (Fin.tail n) k) => z ⟨p.1.succ, p.2⟩) :=
      differentiable_pi.2 fun p => differentiable_apply _
    have hL0 : Differentiable ℂ (fun (z : (Σ k, Bk n k) → ℂ) (i : Fin (n 0 + 1)) => z ⟨0, i⟩) :=
      differentiable_pi.2 fun i => differentiable_apply _
    have hT : Set.MapsTo (fun (z : (Σ k, Bk n k) → ℂ) (p : Σ k, Bk (Fin.tail n) k) => z ⟨p.1.succ, p.2⟩)
        {z | ∀ k, z ⟨k, c k⟩ ≠ 0}
        {z : (Σ k, Bk (Fin.tail n) k) → ℂ | ∀ k, z ⟨k, c k.succ⟩ ≠ 0} := fun z hz k => hz k.succ
    have main := GlobalTheory.CompanionTheory.Ar.ProdHolo.differentiableOn_ev_prod (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) σ₀
      {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} (chart ℤ (n 0) (c 0))
      (mchart (n := Fin.tail n) (fun j => c j.succ))
      (isAffineOpen_chart ℤ (n 0) (c 0)) hA
      (fun z => ptP (n 0) (c 0) (fun i => z ⟨0, i⟩))
      (fun z => multiprojectivePoint (n := Fin.tail n) (fun j => c j.succ) (fun p => z ⟨p.1.succ, p.2⟩))
      (multiprojectivePoint c) (multiprojectivePoint_fst n c) (multiprojectivePoint_snd n c)
      (fun z _ => CxPts.ofHom_mem _ _ _) (fun z hz => hM _ (hT hz))
      (fun a => (GlobalTheory.CompanionTheory.MPSmooth.differentiableOn_ev_ptP (n 0) (c 0) a).comp hL0.differentiableOn fun z hz => hz 0)
      (fun b => (hD b).comp hL.differentiableOn hT)
    have key : ∀ W : (MP ℤ (m + 1) n).Opens,
        W = (pullback.fst (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ chart ℤ (n 0) (c 0) ⊓
          pullback.snd (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ
            mchart (n := Fin.tail n) (fun j => c j.succ) : (MP ℤ (m + 1) n).Opens) → IsAffineOpen W ∧
        (∀ z ∈ {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0}, multiprojectivePoint c z ∈ ptsIn (mpStr ℤ (m + 1) n) σ₀ W) ∧
        ∀ a : Γ(MP ℤ (m + 1) n, W), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ (m + 1) n) σ₀ W a ∘ multiprojectivePoint c)
          {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      rintro W rfl
      exact main
    exact key _ (mchart_succ n c)

/- English proof (translation)
Introduce `m n c` and use `⟨(multiprojective_chart_affine_holomorphic_points m n c).1, (multiprojective_chart_affine_holomorphic_points m n c).2.2⟩`.
-/
theorem mchart_affine_holo : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k), IsAffineOpen (mchart c) ∧
    ∀ a : Γ(MP ℤ m n, mchart c), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) a ∘ GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c)
      {z | ∀ k, z ⟨k, c k⟩ ≠ 0} :=
  fun m n c => ⟨(multiprojective_chart_affine_holomorphic_points m n c).1, (multiprojective_chart_affine_holomorphic_points m n c).2.2⟩

end GlobalTheory.CompanionTheory.MPSmooth
