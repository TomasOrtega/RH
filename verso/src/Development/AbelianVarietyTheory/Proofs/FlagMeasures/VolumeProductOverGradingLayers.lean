import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IpLEqZeroOfMemSpan
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.LayerBox

/- English proof (translation)
Establish `hm : Measurable (fun (x : ι → κ → ℝ) (p : ι × κ) => x p.1 p.2)` using `by fun_prop`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Use `symm`. Apply `Measure.pi_eq` to reduce the goal to its premises. Introduce `s hs`.

Rewrite using `[Measure.map_apply hm (MeasurableSet.univ_pi hs)]`. Establish `: (fun (x : ι → κ → ℝ) (p : ι × κ) => x p.1 p.2) ⁻¹' (Set.univ.pi s) = Set.univ.pi (fun a => Set.univ.pi (fun b => s (a, b)))`. Use extensionality with `y`. Simplify using `[Set.mem_pi]`. Rewrite using `[this, volume_pi_pi, Fintype.prod_prod_type]`.

Simplify using `[volume_pi_pi]`.
-/
theorem pres_uncurry (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (fun (x : ι → κ → ℝ) (p : ι × κ) => x p.1 p.2) volume volume := by
  have hm : Measurable (fun (x : ι → κ → ℝ) (p : ι × κ) => x p.1 p.2) := by
    fun_prop
  refine ⟨hm, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun (x : ι → κ → ℝ) (p : ι × κ) => x p.1 p.2) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi (fun a => Set.univ.pi (fun b => s (a, b))) := by
    ext y; simp [Set.mem_pi]
  rw [this, volume_pi_pi, Fintype.prod_prod_type]
  simp [volume_pi_pi]

/- English proof (translation)
Establish `hm : Measurable (fun (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (p : ι × Fin d) => y ⟨deg p.2, h p.1 p.2⟩ p.1 ⟨p.2, rfl⟩)` using `by fun_prop`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Use `symm`. Apply `Measure.pi_eq` to reduce the goal to its premises. Introduce `s hs`.

Rewrite using `[Measure.map_apply hm (MeasurableSet.univ_pi hs)]`. Establish `: (fun (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (p : ι × Fin d) => y ⟨deg p.2, h p.1 p.2⟩ p.1 ⟨p.2, rfl⟩) ⁻¹' (Set.univ.pi s) = Set.univ.pi (fun c => Set.univ.pi (fun v => Set.univ.pi (fun i => s (v, i.1))))`. Use extensionality with `y`. Simplify using `only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Prod.forall]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `H ⟨c, hc⟩ v ⟨i, hi⟩`. Simplify using `only at hi`. Substitute `hi` using the available equality. Conclude with `H v i`. Introduce `H v i`.

Conclude with `H ⟨deg i, h v i⟩ v ⟨i, rfl⟩`. Rewrite using `[this, volume_pi_pi, Fintype.prod_prod_type]`. Simplify using `only [volume_pi_pi]`. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.prod_fiberwise (s := Finset.univ) (g := fun i => (⟨deg i, h v i⟩ : Fin m))]`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `symm`. Apply `Finset.prod_subtype (f := fun i => volume (s (v, i)))` to reduce the goal to its premises. Introduce `i`.

Simplify using `[Fin.ext_iff]`.
-/
theorem pres_layers (ι : Type) [Fintype ι] (d m : ℕ) (deg : Fin d → ℕ) (h : ι → ∀ i, deg i < m) :
    MeasurePreserving (fun (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (p : ι × Fin d) =>
      y ⟨deg p.2, h p.1 p.2⟩ p.1 ⟨p.2, rfl⟩) volume volume := by
  have hm : Measurable (fun (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (p : ι × Fin d) =>
      y ⟨deg p.2, h p.1 p.2⟩ p.1 ⟨p.2, rfl⟩) := by
    fun_prop
  refine ⟨hm, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (p : ι × Fin d) =>
      y ⟨deg p.2, h p.1 p.2⟩ p.1 ⟨p.2, rfl⟩) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi (fun c => Set.univ.pi (fun v => Set.univ.pi (fun i => s (v, i.1)))) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Prod.forall]
    constructor
    · rintro H ⟨c, hc⟩ v ⟨i, hi⟩
      simp only at hi
      subst hi
      exact H v i
    · intro H v i
      exact H ⟨deg i, h v i⟩ v ⟨i, rfl⟩
  rw [this, volume_pi_pi, Fintype.prod_prod_type]
  simp only [volume_pi_pi]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_fiberwise (s := Finset.univ) (g := fun i => (⟨deg i, h v i⟩ : Fin m))]
  refine Finset.prod_congr rfl fun c _ => ?_
  symm
  apply Finset.prod_subtype (f := fun i => volume (s (v, i)))
  intro i
  simp [Fin.ext_iff]

/- English proof (translation)
Introduce `ι _ d m deg D h hD`. Set `F : Set (ι × Fin d → ℝ)` to `{z | ∀ c < m, (fun v (i : {i : Fin d // deg i = c}) => z (v, i.1)) ∈ D c}`. Establish `hF : MeasurableSet F`. Establish `: F = ⋂ c, ⋂ (_ : c < m), (fun (z : ι × Fin d → ℝ) v (i : {i : Fin d // deg i = c}) => z (v, i.1)) ⁻¹' D c`. Use extensionality with `z`.

Simplify using `[F]`. Rewrite using `[this]`. Use `MeasurableSet.iInter fun c => MeasurableSet.iInter fun _ => ?_` and prove the remaining obligations. Conclude with `(hD c).preimage (by fun_prop)`. Establish `h1` using `(pres_uncurry ι (Fin d)).measure_preimage hF.nullMeasurableSet`.

Establish `h2` using `(pres_layers ι d m deg h).measure_preimage hF.nullMeasurableSet`. Establish `key : ∀ (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (c : ℕ) (hc : c < m), (fun v (i : {i : Fin d // deg i = c}) => y ⟨deg i.1, h v i.1⟩ v ⟨i.1, rfl⟩) = y ⟨c, hc⟩`. Introduce `y c hc`. Use function extensionality and compare the values at `v i`. Take `⟨i, hi⟩` from `i`.

Substitute `hi` using the available equality. Both sides reduce to the same expression. Establish `h3 : (fun (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (p : ι × Fin d) => y ⟨deg p.2, h p.1 p.2⟩ p.1 ⟨p.2, rfl⟩) ⁻¹' F = Set.univ.pi (fun c : Fin m => D c)`. Use extensionality with `y`. Simplify using `only [F, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]`.

Prove the components needed by the constructor for the conclusion. Introduce `H c`. Use `H c c.2` as an intermediate fact. Rewrite `this` using `[key y c c.2]`. Then use the resulting hypothesis. Introduce `H c hc`.

Rewrite using `[key y c hc]`. Conclude with `H ⟨c, hc⟩`. Rewrite `h2` using `[h3, volume_pi_pi, Fin.prod_univ_eq_prod_range (fun c => volume (D c))]`. Rewrite using `[h2, ← h1]`. Both sides reduce to the same expression.
-/
theorem volume_layer_box : ∀ (ι : Type) [Fintype ι] (d m : ℕ) (deg : Fin d → ℕ) (D : ∀ c : ℕ, Set (ι → {i : Fin d // deg i = c} → ℝ)), (ι → ∀ i, deg i < m) → (∀ c, MeasurableSet (D c)) → volume {x : ι → Fin d → ℝ | ∀ c < m, (fun v (i : {i : Fin d // deg i = c}) => x v i.1) ∈ D c} = ∏ c ∈ Finset.range m, volume (D c) := by
  intro ι _ d m deg D h hD
  let F : Set (ι × Fin d → ℝ) :=
    {z | ∀ c < m, (fun v (i : {i : Fin d // deg i = c}) => z (v, i.1)) ∈ D c}
  have hF : MeasurableSet F := by
    have : F = ⋂ c, ⋂ (_ : c < m),
        (fun (z : ι × Fin d → ℝ) v (i : {i : Fin d // deg i = c}) => z (v, i.1)) ⁻¹' D c := by
      ext z; simp [F]
    rw [this]
    refine MeasurableSet.iInter fun c => MeasurableSet.iInter fun _ => ?_
    exact (hD c).preimage (by fun_prop)
  have h1 := (pres_uncurry ι (Fin d)).measure_preimage hF.nullMeasurableSet
  have h2 := (pres_layers ι d m deg h).measure_preimage hF.nullMeasurableSet
  have key : ∀ (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (c : ℕ) (hc : c < m),
      (fun v (i : {i : Fin d // deg i = c}) => y ⟨deg i.1, h v i.1⟩ v ⟨i.1, rfl⟩) = y ⟨c, hc⟩ := by
    intro y c hc
    funext v i
    obtain ⟨i, hi⟩ := i
    subst hi
    rfl
  have h3 : (fun (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (p : ι × Fin d) =>
      y ⟨deg p.2, h p.1 p.2⟩ p.1 ⟨p.2, rfl⟩) ⁻¹' F = Set.univ.pi (fun c : Fin m => D c) := by
    ext y
    simp only [F, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro H c
      have := H c c.2
      rwa [key y c c.2] at this
    · intro H c hc
      rw [key y c hc]
      exact H ⟨c, hc⟩
  rw [h3, volume_pi_pi, Fin.prod_univ_eq_prod_range (fun c => volume (D c))] at h2
  rw [h2, ← h1]
  rfl

end GlobalTheory.LayerBox
