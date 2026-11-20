import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacuumLine

open GlobalTheory.FockCompare GlobalTheory.VacUnique

/- English proof (translation)
Introduce `D ψ θ S T sS sT ΛS ΛT f₀ hb f hf hlat hfock`. Establish `hne : f₀ ≠ 0` using `GlobalTheory.PlaceTensor.base_ne_zero hb`. Take `⟨hS, hT, dS, dT, hψ, hθ, ht₀, hl₀, hF₀, -⟩` from `hb`. Establish `hψn : ∀ x, ‖ψ x‖ = 1` using `hψ.1.2.1`. Take `⟨ρ, hρc, hρ1, hρ2⟩` from `GlobalTheory.FockCompare.exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)`.

Take `⟨σ, hσ⟩` from `GlobalTheory.FockCompare.RealChart.exists_chart D θ hθ ρ hρc hρ1 hρ2`. Take `⟨hdual, hdec, heig⟩` from `GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ dS dT`. Use `set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ`. Establish `hinf : ∀ u ∈ Λ, u.map (infPart D) = 0` using `fun u hu => GlobalTheory.VacUnique.latO_inf S T _ _ _ hu`. Establish `key : ∀ u ∈ Λ, ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ heisO ψ S T u f = ε • f ∧ heisO ψ S T u f₀ = ε • f₀`.

Introduce `u hu`. Take `⟨ε, hε, h⟩` from `heig f hlat u hu`. Conclude with `⟨ε, hε, h f hlat, h f₀ hl₀⟩`. Establish `ext : ∀ w, ∃ z : RW T S, ∃ a : ℂ, f w = a * f (iotaW σ T S z) ∧ f₀ w = a * f₀ (iotaW σ T S z)`. Introduce `w`.

Take `⟨γ, z, u, hu, rfl⟩` from `GlobalTheory.VacUnique.exists_decomp hσ hdec w`. Take `⟨ε, -, h1, h2⟩` from `key u hu`. Use `⟨z, ψ (-symplOH S T (ratW T S γ) (iotaW σ T S z + u)) * ε, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hf.1 γ, GlobalTheory.VacUnique.apply_real_add hσ hψ (hinf u hu) h1 z]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[ht₀.1 γ, GlobalTheory.VacUnique.apply_real_add hσ hψ (hinf u hu) h2 z]`. Expand and normalize the polynomial expressions, which then agree. Establish `hN : ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ Λ` using `GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT dS.1 dT.1`. Establish `hLd` using `GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff D S T ψ Λ hψ hinf hdual hdec hN`. Take `⟨hJ, hanti, hinv, hpos⟩` from `GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT`.

Set `c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ` to `fun v => if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * (key _ hv).choose else 1`. Establish `hc : ∀ v, ‖c v‖ = 1`. Introduce `v`. Simplify using `only [c]`. Use `split_ifs with hv`.

Rewrite using `[norm_mul, hψn, one_mul]`. Apply the tactic sequence `rcases (key _ hv).choose_spec.1 with h | h <;> rw [h] <;> simp`. Simplify using the standard rewrite rules. Establish `hfd` using `GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ hσ ψ hψ S T sS sT f hf hfock`. Establish `hfd₀` using `GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ hσ ψ hψ S T sS sT f₀ ht₀ hF₀`.

Establish `hspan : Submodule.span ℝ (Set.range (infRat S T)) = ⊤`. Use `GlobalTheory.FockCompare.span_piW_ratW_eq_top D θ σ hσ T S` as an intermediate fact. Simplify `this` using `[GlobalTheory.VacUnique.piW_ratW hθ]`. Establish `hli` using `GlobalTheory.T.not_linearIndependent_alt (RW T S) (jO S T sS sT) (omO S T) hJ hanti hinv hpos (Matrix (Fin T.rank) (Fin S.rank) D.host.E) (infRat S T) (GlobalTheory.VacUnique.infRat_injective S T) hspan (Λ.comap (finRat S T)) (fun x => by simpa using hN x) (fun x => by simpa usin …`. Use `case fock => exact Fin.forall_fin_two.2 ⟨hfd₀.2, hfd.2⟩`.

Use `case quasi =>`. Introduce `k v hv z`. Establish `hv' : finRat S T (-v) ∈ Λ`. Rewrite using `[map_neg]`. Conclude with `Λ.neg_mem (AddSubgroup.mem_comap.1 hv)`.

Establish `hcv : c v = ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * (key _ hv').choose`. Simplify using `only [c, dif_pos hv']`. Take `⟨-, h1, h2⟩` from `(key _ hv').choose_spec`. Establish `e1` using `GlobalTheory.VacUnique.apply_add_infRat hσ hψ hf v h1 z`. Establish `e2` using `GlobalTheory.VacUnique.apply_add_infRat hσ hψ ht₀ v h2 z`.

Establish `ho : (omO S T z (infRat S T v) : ℂ) = ((-omO S T (infRat S T v) z : ℝ) : ℂ)` using `by rw [hanti]`. Rewrite using `[hcv, ho]`. Use `fin_cases k`. Conclude with `e2`. Conclude with `e1`.

Rewrite `hli` using `[LinearIndependent.pair_iff]`. Use `push_neg at hli`. Take `⟨s, t, hst, hne0⟩` from `hli`. Establish `hpt : ∀ z, s * f₀ (iotaW σ T S z) + t * f (iotaW σ T S z) = 0` using `fun z => by`. Use `congrFun hst z` as an intermediate fact.

Simplify using `using this`. Distinguish the cases in `ht : t = 0`. It suffices to derive a contradiction. Establish `hs : s ≠ 0` using `fun hs => hne0 hs ht`. Apply `hne` to reduce the goal to its premises.

Use function extensionality and compare the values at `w`. Take `⟨z, a, -, h2⟩` from `ext w`. Use `hpt z` as an intermediate fact. Rewrite `this` using `[ht, zero_mul, add_zero]`. Rewrite using `[h2, (mul_eq_zero.1 this).resolve_left hs]`.

Simplify using the standard rewrite rules. Use `⟨-s / t, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Take `⟨z, a, h1, h2⟩` from `ext w`. Use `hpt z` as an intermediate fact.

Rewrite using `[Pi.smul_apply, smul_eq_mul, h1, h2, div_mul_eq_mul_div, eq_div_iff ht]`. Take the linear combination `a * this`.
-/
theorem eq_smul_base : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → ∃ c : ℂ, f = c • f₀ := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ hb f hf hlat hfock
  have hne : f₀ ≠ 0 := GlobalTheory.PlaceTensor.base_ne_zero hb
  obtain ⟨hS, hT, dS, dT, hψ, hθ, ht₀, hl₀, hF₀, -⟩ := hb
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  obtain ⟨ρ, hρc, hρ1, hρ2⟩ := GlobalTheory.FockCompare.exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.RealChart.exists_chart D θ hθ ρ hρc hρ1 hρ2
  obtain ⟨hdual, hdec, heig⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ dS dT
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  have hinf : ∀ u ∈ Λ, u.map (infPart D) = 0 := fun u hu => GlobalTheory.VacUnique.latO_inf S T _ _ _ hu
  have key : ∀ u ∈ Λ, ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ heisO ψ S T u f = ε • f ∧ heisO ψ S T u f₀ = ε • f₀ := by
    intro u hu
    obtain ⟨ε, hε, h⟩ := heig f hlat u hu
    exact ⟨ε, hε, h f hlat, h f₀ hl₀⟩
  have ext : ∀ w, ∃ z : RW T S, ∃ a : ℂ, f w = a * f (iotaW σ T S z) ∧ f₀ w = a * f₀ (iotaW σ T S z) := by
    intro w
    obtain ⟨γ, z, u, hu, rfl⟩ := GlobalTheory.VacUnique.exists_decomp hσ hdec w
    obtain ⟨ε, -, h1, h2⟩ := key u hu
    refine ⟨z, ψ (-symplOH S T (ratW T S γ) (iotaW σ T S z + u)) * ε, ?_, ?_⟩
    · rw [hf.1 γ, GlobalTheory.VacUnique.apply_real_add hσ hψ (hinf u hu) h1 z]; ring
    · rw [ht₀.1 γ, GlobalTheory.VacUnique.apply_real_add hσ hψ (hinf u hu) h2 z]; ring
  have hN : ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ Λ :=
    GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT dS.1 dT.1
  have hLd := GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff D S T ψ Λ hψ hinf hdual hdec hN
  obtain ⟨hJ, hanti, hinv, hpos⟩ := GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT
  classical
  let c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ := fun v =>
    if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * (key _ hv).choose else 1
  have hc : ∀ v, ‖c v‖ = 1 := by
    intro v
    simp only [c]
    split_ifs with hv
    · rw [norm_mul, hψn, one_mul]
      rcases (key _ hv).choose_spec.1 with h | h <;> rw [h] <;> simp
    · simp
  have hfd := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ hσ ψ hψ S T sS sT f hf hfock
  have hfd₀ := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ hσ ψ hψ S T sS sT f₀ ht₀ hF₀
  have hspan : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
    have := GlobalTheory.FockCompare.span_piW_ratW_eq_top D θ σ hσ T S
    simpa [GlobalTheory.VacUnique.piW_ratW hθ] using this
  have hli := GlobalTheory.T.not_linearIndependent_alt (RW T S) (jO S T sS sT) (omO S T) hJ hanti hinv hpos
    (Matrix (Fin T.rank) (Fin S.rank) D.host.E) (infRat S T) (GlobalTheory.VacUnique.infRat_injective S T) hspan
    (Λ.comap (finRat S T)) (fun x => by simpa using hN x) (fun x => by simpa using hLd x) c hc
    ![fun z => f₀ (iotaW σ T S z), fun z => f (iotaW σ T S z)]
    (Fin.forall_fin_two.2 ⟨hfd₀.1, hfd.1⟩) ?fock ?quasi
  case fock => exact Fin.forall_fin_two.2 ⟨hfd₀.2, hfd.2⟩
  case quasi =>
    intro k v hv z
    have hv' : finRat S T (-v) ∈ Λ := by
      rw [map_neg]
      exact Λ.neg_mem (AddSubgroup.mem_comap.1 hv)
    have hcv : c v = ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * (key _ hv').choose := by
      simp only [c, dif_pos hv']
    obtain ⟨-, h1, h2⟩ := (key _ hv').choose_spec
    have e1 := GlobalTheory.VacUnique.apply_add_infRat hσ hψ hf v h1 z
    have e2 := GlobalTheory.VacUnique.apply_add_infRat hσ hψ ht₀ v h2 z
    have ho : (omO S T z (infRat S T v) : ℂ) = ((-omO S T (infRat S T v) z : ℝ) : ℂ) := by rw [hanti]
    rw [hcv, ho]
    fin_cases k
    · exact e2
    · exact e1
  rw [LinearIndependent.pair_iff] at hli
  push_neg at hli
  obtain ⟨s, t, hst, hne0⟩ := hli
  have hpt : ∀ z, s * f₀ (iotaW σ T S z) + t * f (iotaW σ T S z) = 0 := fun z => by
    have := congrFun hst z
    simpa using this
  by_cases ht : t = 0
  · exfalso
    have hs : s ≠ 0 := fun hs => hne0 hs ht
    apply hne
    funext w
    obtain ⟨z, a, -, h2⟩ := ext w
    have := hpt z
    rw [ht, zero_mul, add_zero] at this
    rw [h2, (mul_eq_zero.1 this).resolve_left hs]
    simp
  · refine ⟨-s / t, ?_⟩
    funext w
    obtain ⟨z, a, h1, h2⟩ := ext w
    have := hpt z
    rw [Pi.smul_apply, smul_eq_mul, h1, h2, div_mul_eq_mul_div, eq_div_iff ht]
    linear_combination a * this

end GlobalTheory.VacuumLine

end
