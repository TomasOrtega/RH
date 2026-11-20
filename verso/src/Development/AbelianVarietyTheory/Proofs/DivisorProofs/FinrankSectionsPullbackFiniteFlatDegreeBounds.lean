import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

open FiniteCover

/- English proof (translation)
Introduce `K _ X X' _ _ f φ _ _ _ H n s hH hs d hd hV hW`. Establish `hd1 : 1 ≤ d` using `hd _ ▸ φ.one_le_finrank_map (genericPoint X')`. Use `letI : Algebra X.functionField X'.functionField := (functionFieldMap φ).toAlgebra`. Use `letI : Algebra K X.functionField := ((toField generic_top).comp (cst f ⊤)).toAlgebra`. Use `letI : Algebra K X'.functionField := ((toField generic_top).comp (cst (φ ≫ f) ⊤)).toAlgebra`.

Use `haveI : IsScalarTower K X.functionField X'.functionField := IsScalarTower.of_algebraMap_eq fun r => by`. Establish `w : φ ≫ f = (φ ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id K))` using `by simp`. Establish `e` using `toField_appLE φ (U := ⊤) (V := ⊤) le_top generic_top generic_top (cst f ⊤ r)`. Conclude with `(congrArg (toField generic_top) (appLE_cst w (V := ⊤) (V' := ⊤) le_top r)).symm.trans e`. Take `⟨hcov, hs⟩` from `hs`.

Use `choose haff r hr _ using hs`. Set `I` to `{i // genericPoint X ∈ nonzeroLocus (s i)}`. Use `haveI : Fintype I := Fintype.ofFinite I`. Set `D : I → X.Opens` to `fun i => nonzeroLocus (s i.1)`. Establish `hη : ∀ i, genericPoint X ∈ D i` using `fun i => i.2`.

Establish `hc : ⊤ ≤ ⨆ i, D i` using `fun x hx => by`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hcov.ge hx)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, generic_mem hi⟩, hi⟩`. Establish `hc' : ⊤ ≤ ⨆ i, φ ⁻¹ᵁ D i` using `fun x _ => by`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hc (trivial : φ x ∈ ⊤))`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩`. Take `⟨i₀, -⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)`. Take `⟨k₀, h₀⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge generic_top)`. Take `⟨x, hx⟩` from `(chart_data φ (fun _ => rfl) (haff i₀.1) (hη i₀)).1`. Rewrite `hx` using `[hd]`.

Use `haveI : Module.Finite X.functionField X'.functionField := Module.finite_of_finrank_pos (by omega)`. Set `e` to `Module.finBasisOfFinrankEq _ _ hx`. Use `choose c hcm hc0 hc₁ hc₂ using fun i : I => (chart_data φ (fun _ => rfl) (haff i.1) (hη i)).2 e`. Set `ρ : I → X.functionField` to `fun i => toField h₀ ((s i.1).f k₀)`. Establish `hu : ∀ (i : I) k, IsUnit (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k))` using `fun i k => SecOn.isUnit_rs_of_le_nonzeroLocus _ k _ inf_le_left`.

Establish `hρ : ∀ i, ρ i ≠ 0` using `fun i => by`. Use `((hu i k₀).map (toField (generic_inf (hη i) h₀))).ne_zero` as an intermediate fact. Rewrite `this` using `[toField_rs]`. Then use the resulting hypothesis. Establish `hρr : ∀ i k : I, ρ i / ρ k = toField (hη k) (r k.1 i.1)` using `fun i k => by`. Use `congrArg (toField (generic_inf (hη k) h₀)) (hr k.1 i.1 k₀)` as an intermediate fact.

Rewrite `this` using `[map_mul, toField_rs, toField_rs, toField_rs]`. Conclude with `(div_eq_iff (hρ k)).2 this`. Set `τ : ∀ (t : ℕ) (i : I), SecOn (pw H t) (D i)` to `fun t i => GlobalTheory.LB.ofSec (powSec (s i.1) t) (D i)`. Establish `hτc : ∀ (t : ℕ) (i : I) (k : H.ι), GlobalTheory.LB.coord (τ t i) k = rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k) ^ t` using `fun t i k => (GlobalTheory.LB.coord_ofSec _ _ _).trans (map_pow (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k)) _ _)`. Establish `hτ : ∀ (t : ℕ) (i : I) (k : H.ι), IsUnit (GlobalTheory.LB.coord (τ t i) k)` using `fun t i k => (hτc t i k).symm ▸ (hu i k).pow t`.

Establish `hτv : ∀ (t : ℕ) (i : I), secVal (M` using `pw H t) (k₀ := k₀) h₀ (hη i) (τ t i) = ρ i ^ t := fun t i => (congrArg (toField (generic_inf (hη i) h₀)) (hτc t i k₀)).trans (by`. Rewrite using `[map_pow, toField_rs])`. Establish `h₀' : ∀ t : ℕ, genericPoint X' ∈ ((pw H t).pull φ).U fun _ => k₀` using `fun t => le_pull (pw H t) φ (i := k₀) le_rfl (generic_mem_preimage φ h₀)`. Use `finrank_sandwich e (fun i => (toField (hη i)).range) (fun i => (toField (generic_mem_preimage φ (hη i))).range) ρ c hρ hc0 (fun i k => ⟨_, (hρr i k).symm⟩) (fun i k => ?_) ?_ hc₁ hc₂ (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) hV hW (fun t => secV …` and prove the remaining obligations. Take `⟨a, ha⟩` from `hcm i`.

Rewrite using `[← ha, hρr]`. Conclude with `exists_mul_pow_mem (haff k.1) (hη k) (hη i) _ (hρr i k ▸ div_ne_zero (hρ i) (hρ k)) (FiniteCover.basicOpen_le_nonzeroLocus _ _ _ (hr k.1 i.1)) a`. Introduce and unpack `i _ ⟨a, rfl⟩`. Conclude with `⟨_, toField_appLE φ le_rfl (hη i) _ a⟩`. Use `(exists_secVal_eq_iff (M := pw H t) (k₀ := k₀) h₀ (isLB_pw hH t) D hc hη (τ t) (hτ t) x).trans ?_` and prove the remaining obligations.

Simplify using `only [hτv]`. Use `(exists_secVal_eq_iff (h₀' t) (LB.isLB_pull (isLB_pw hH t) φ) (fun i => φ ⁻¹ᵁ D i) hc' (fun i => generic_mem_preimage φ (hη i)) (fun i => SecOn.pull (pw H t) φ (D i) (τ t i)) (fun i k => (hτ t i (k PUnit.unit)).map _) y).trans ?_` and prove the remaining obligations. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[secVal_pull (M := pw H t) (k₀ := k₀) h₀ φ (hη i), hτv]`. Both sides reduce to the same expression.
-/
theorem finrank_sec_pull_sandwich_flat : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  intro K _ X X' _ _ f φ _ _ _ H n s hH hs d hd hV hW
  have hd1 : 1 ≤ d := hd _ ▸ φ.one_le_finrank_map (genericPoint X')
  letI : Algebra X.functionField X'.functionField := (functionFieldMap φ).toAlgebra
  letI : Algebra K X.functionField := ((toField generic_top).comp (cst f ⊤)).toAlgebra
  letI : Algebra K X'.functionField := ((toField generic_top).comp (cst (φ ≫ f) ⊤)).toAlgebra
  haveI : IsScalarTower K X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      have w : φ ≫ f = (φ ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) := by simp
      have e := toField_appLE φ (U := ⊤) (V := ⊤) le_top generic_top generic_top (cst f ⊤ r)
      exact (congrArg (toField generic_top)
        (appLE_cst w (V := ⊤) (V' := ⊤) le_top r)).symm.trans e
  obtain ⟨hcov, hs⟩ := hs
  choose haff r hr _ using hs
  let I := {i // genericPoint X ∈ nonzeroLocus (s i)}
  haveI : Fintype I := Fintype.ofFinite I
  let D : I → X.Opens := fun i => nonzeroLocus (s i.1)
  have hη : ∀ i, genericPoint X ∈ D i := fun i => i.2
  have hc : ⊤ ≤ ⨆ i, D i := fun x hx => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, generic_mem hi⟩, hi⟩
  have hc' : ⊤ ≤ ⨆ i, φ ⁻¹ᵁ D i := fun x _ => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (trivial : φ x ∈ ⊤))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨i₀, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)
  obtain ⟨k₀, h₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge generic_top)
  obtain ⟨x, hx⟩ := (chart_data φ (fun _ => rfl) (haff i₀.1) (hη i₀)).1
  rw [hd] at hx
  haveI : Module.Finite X.functionField X'.functionField :=
    Module.finite_of_finrank_pos (by omega)
  let e := Module.finBasisOfFinrankEq _ _ hx
  choose c hcm hc0 hc₁ hc₂ using fun i : I =>
    (chart_data φ (fun _ => rfl) (haff i.1) (hη i)).2 e
  let ρ : I → X.functionField := fun i => toField h₀ ((s i.1).f k₀)
  have hu : ∀ (i : I) k, IsUnit (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k)) :=
    fun i k => SecOn.isUnit_rs_of_le_nonzeroLocus _ k _ inf_le_left
  have hρ : ∀ i, ρ i ≠ 0 := fun i => by
    have := ((hu i k₀).map (toField (generic_inf (hη i) h₀))).ne_zero
    rwa [toField_rs] at this
  have hρr : ∀ i k : I, ρ i / ρ k = toField (hη k) (r k.1 i.1) := fun i k => by
    have := congrArg (toField (generic_inf (hη k) h₀)) (hr k.1 i.1 k₀)
    rw [map_mul, toField_rs, toField_rs, toField_rs] at this
    exact (div_eq_iff (hρ k)).2 this
  let τ : ∀ (t : ℕ) (i : I), SecOn (pw H t) (D i) := fun t i => GlobalTheory.LB.ofSec (powSec (s i.1) t) (D i)
  have hτc : ∀ (t : ℕ) (i : I) (k : H.ι), GlobalTheory.LB.coord (τ t i) k =
      rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k) ^ t := fun t i k =>
    (GlobalTheory.LB.coord_ofSec _ _ _).trans (map_pow (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k)) _ _)
  have hτ : ∀ (t : ℕ) (i : I) (k : H.ι), IsUnit (GlobalTheory.LB.coord (τ t i) k) := fun t i k =>
    (hτc t i k).symm ▸ (hu i k).pow t
  have hτv : ∀ (t : ℕ) (i : I), secVal (M := pw H t) (k₀ := k₀) h₀ (hη i) (τ t i) = ρ i ^ t :=
    fun t i => (congrArg (toField (generic_inf (hη i) h₀)) (hτc t i k₀)).trans (by
      rw [map_pow, toField_rs])
  have h₀' : ∀ t : ℕ, genericPoint X' ∈ ((pw H t).pull φ).U fun _ => k₀ := fun t =>
    le_pull (pw H t) φ (i := k₀) le_rfl (generic_mem_preimage φ h₀)
  refine finrank_sandwich e (fun i => (toField (hη i)).range)
    (fun i => (toField (generic_mem_preimage φ (hη i))).range) ρ c hρ hc0
    (fun i k => ⟨_, (hρr i k).symm⟩) (fun i k => ?_) ?_ hc₁ hc₂
    (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) hV hW
    (fun t => secValLin (M := pw H t) (k₀ := k₀) h₀ f fun _ => rfl)
    (fun t => secValLin (h₀' t) (φ ≫ f) fun _ => rfl)
    (fun t => secVal_injective (M := pw H t) (k₀ := k₀) h₀ generic_top)
    (fun t => secVal_injective (h₀' t) generic_top) (fun t x => ?_) fun t y => ?_
  · obtain ⟨a, ha⟩ := hcm i
    rw [← ha, hρr]
    exact exists_mul_pow_mem (haff k.1) (hη k) (hη i) _
      (hρr i k ▸ div_ne_zero (hρ i) (hρ k)) (FiniteCover.basicOpen_le_nonzeroLocus _ _ _ (hr k.1 i.1)) a
  · rintro i _ ⟨a, rfl⟩
    exact ⟨_, toField_appLE φ le_rfl (hη i) _ a⟩
  · refine (exists_secVal_eq_iff (M := pw H t) (k₀ := k₀) h₀ (isLB_pw hH t) D hc hη (τ t) (hτ t)
      x).trans ?_
    simp only [hτv]
  · refine (exists_secVal_eq_iff (h₀' t) (LB.isLB_pull (isLB_pw hH t) φ) (fun i => φ ⁻¹ᵁ D i) hc'
      (fun i => generic_mem_preimage φ (hη i)) (fun i => SecOn.pull (pw H t) φ (D i) (τ t i))
      (fun i k => (hτ t i (k PUnit.unit)).map _) y).trans ?_
    refine forall_congr' fun i => ?_
    rw [secVal_pull (M := pw H t) (k₀ := k₀) h₀ φ (hη i), hτv]
    rfl

end GlobalTheory
