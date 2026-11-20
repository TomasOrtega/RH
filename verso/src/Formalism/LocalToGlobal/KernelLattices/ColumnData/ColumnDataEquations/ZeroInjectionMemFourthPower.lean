import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNoEig
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.FinitelyGeneratedModPow

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

section Gen

variable {n : Type} [Fintype n]

def inj0 (n : Type) : (n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ) where
  toFun x := fun w => if w.1 = 0 then x w.2 else 0
  map_add' x y := by funext w; by_cases h : w.1 = 0 <;> simp [h]
  map_smul' c x := by funext w; by_cases h : w.1 = 0 <;> simp [h]

def sl0 (n : Type) : (Fin 4 × n → ℂ) →ₗ[ℂ] (n → ℂ) where
  toFun z := slice 0 z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases h : a = 0 <;> simp [slice, inj0, h]`.
-/
theorem slice_zero_injection (x : n → ℂ) (a : Fin 4) : slice a (inj0 n x) = if a = 0 then x else 0 := by
  funext i
  by_cases h : a = 0 <;> simp [slice, inj0, h]

/- English proof (translation)
Introduce `a`. Rewrite using `[slice_zero_injection]`. Use `split_ifs`. Conclude with `hx`. Conclude with `ΛM.zero_mem`.
-/
theorem zero_injection_mem_fourth_power (ΛM : AddSubgroup (n → ℂ)) {x : n → ℂ} (hx : x ∈ ΛM) : inj0 n x ∈ pow4 ΛM := by
  intro a
  rw [slice_zero_injection]
  split_ifs
  · exact hx
  · exact ΛM.zero_mem

/- English proof (translation)
Take `⟨hd, hs⟩` from `h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `haveI := hd`. Set `φ : ΛM → imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM)` to `fun x => ⟨g (inj0 n x), ⟨inj0 n x, zero_injection_mem_fourth_power ΛM x.2, rfl⟩⟩`. Establish `hφc : Continuous φ`.

Apply `Continuous.subtype_mk` to reduce the goal to its premises. Conclude with `((g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)).comp (inj0 n)).continuous_of_finiteDimensional.comp continuous_subtype_val`. Establish `hφi : Function.Injective φ`. Introduce `x y hxy`. Establish `h1` using `congrArg Subtype.val hxy`.

Establish `h2` using `g.injective h1`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h3` using `congrArg (slice 0) h2`. Rewrite `h3` using `[slice_zero_injection, slice_zero_injection, if_pos rfl, if_pos rfl]`. Then use the resulting hypothesis. Conclude with `DiscreteTopology.of_continuous_injective hφc hφi`.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Set `G : (Fin 4 × n → ℂ) →ₗ[ℝ] (n → ℂ)` to `((sl0 n).comp g.symm.toLinearMap).restrictScalars ℝ`. Establish `hG : ∀ y ∈ (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) : Set _), G y ∈ ΛM`. Introduce and unpack `_ ⟨z, hz, rfl⟩`.

Use `show slice 0 (g.symm (g z)) ∈ ΛM`. Rewrite using `[g.symm_apply_apply]`. Conclude with `hz 0`. Establish `hmap : Submodule.map G (Submodule.span ℝ (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) : Set _)) ≤ Submodule.span ℝ (ΛM : Set (n → ℂ))`. Rewrite using `[Submodule.map_span]`.

Conclude with `Submodule.span_mono (by rintro _ ⟨y, hy, rfl⟩; exact hG y hy)`. Rewrite `hmap` using `[hs, Submodule.map_top]`. Apply `hmap` to reduce the goal to its premises. Use `⟨g (inj0 n x), ?_⟩` and prove the remaining obligations. Use `show slice 0 (g.symm (g (inj0 n x))) = x`.

Rewrite using `[g.symm_apply_apply, slice_zero_injection, if_pos rfl]`.
-/
theorem is_lattice_of_fourth_power (ΛM : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (h : IsLat (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM))) : IsLat ΛM := by
  obtain ⟨hd, hs⟩ := h
  refine ⟨?_, ?_⟩
  · haveI := hd
    let φ : ΛM → imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) :=
      fun x => ⟨g (inj0 n x), ⟨inj0 n x, zero_injection_mem_fourth_power ΛM x.2, rfl⟩⟩
    have hφc : Continuous φ := by
      apply Continuous.subtype_mk
      exact ((g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)).comp (inj0 n)).continuous_of_finiteDimensional.comp
        continuous_subtype_val
    have hφi : Function.Injective φ := by
      intro x y hxy
      have h1 := congrArg Subtype.val hxy
      have h2 := g.injective h1
      apply Subtype.ext
      have h3 := congrArg (slice 0) h2
      rwa [slice_zero_injection, slice_zero_injection, if_pos rfl, if_pos rfl] at h3
    exact DiscreteTopology.of_continuous_injective hφc hφi
  · rw [eq_top_iff]
    intro x _
    let G : (Fin 4 × n → ℂ) →ₗ[ℝ] (n → ℂ) := ((sl0 n).comp g.symm.toLinearMap).restrictScalars ℝ
    have hG : ∀ y ∈ (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) : Set _), G y ∈ ΛM := by
      rintro _ ⟨z, hz, rfl⟩
      show slice 0 (g.symm (g z)) ∈ ΛM
      rw [g.symm_apply_apply]
      exact hz 0
    have hmap : Submodule.map G (Submodule.span ℝ
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) : Set _)) ≤
        Submodule.span ℝ (ΛM : Set (n → ℂ)) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono (by rintro _ ⟨y, hy, rfl⟩; exact hG y hy)
    rw [hs, Submodule.map_top] at hmap
    apply hmap
    refine ⟨g (inj0 n x), ?_⟩
    show slice 0 (g.symm (g (inj0 n x))) = x
    rw [g.symm_apply_apply, slice_zero_injection, if_pos rfl]

def putL (n : Type) (N N' : ℕ) (k : Fin N' × Fin N) : (n → ℂ) →ₗ[ℂ] (n → Fin N' → Fin N → ℂ) where
  toFun x := fun τ i j => if (i, j) = k then x τ else 0
  map_add' x y := by funext τ i j; by_cases h : (i, j) = k <;> simp [h]
  map_smul' c x := by funext τ i j; by_cases h : (i, j) = k <;> simp [h]

/- English proof (translation)
Introduce `i j`. Distinguish the cases in `h : (i, j) = k`. Establish `e : (fun τ => putL n N N' k x τ i j) = x`. Use function extensionality and compare the values at `τ`. Simplify using `[putL, h]`.

Rewrite using `[e]`. Conclude with `hx`. Establish `e : (fun τ => putL n N N' k x τ i j) = 0`. Use function extensionality and compare the values at `τ`. Simplify using `[putL, h]`.

Rewrite using `[e]`. Conclude with `ΛM.zero_mem`.
-/
theorem putL_mem (ΛM : AddSubgroup (n → ℂ)) (N N' : ℕ) (k : Fin N' × Fin N) {x : n → ℂ} (hx : x ∈ ΛM) :
    putL n N N' k x ∈ Ker.powLat ΛM N N' := by
  intro i j
  by_cases h : (i, j) = k
  · have e : (fun τ => putL n N N' k x τ i j) = x := by
      funext τ
      simp [putL, h]
    rw [e]
    exact hx
  · have e : (fun τ => putL n N N' k x τ i j) = 0 := by
      funext τ
      simp [putL, h]
    rw [e]
    exact ΛM.zero_mem

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[putL, Finset.sum_apply]`.
-/
theorem sum_putL (N N' : ℕ) (z : n → Fin N' → Fin N → ℂ) :
    z = ∑ k : Fin N' × Fin N, putL n N N' k (fun τ => z τ k.1 k.2) := by
  funext τ i j
  simp [putL, Finset.sum_apply]

/- English proof (translation)
Take `⟨hd, hs⟩` from `h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `haveI := hd`. Set `ψ : Ker.powLat ΛM N N' → (Fin N' × Fin N → ΛM)` to `fun z k => ⟨fun τ => z.1 τ k.1 k.2, z.2 k.1 k.2⟩`. Establish `hψc : Continuous ψ`.

Apply `continuous_pi` to reduce the goal to its premises. Introduce `k`. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Apply `continuous_pi` to reduce the goal to its premises. Introduce `τ`.

Establish `hc : Continuous (fun z : Ker.powLat ΛM N N' => (z : n → Fin N' → Fin N → ℂ))` using `continuous_subtype_val`. Establish `hc1 : Continuous (fun z : Ker.powLat ΛM N N' => (z : n → Fin N' → Fin N → ℂ) τ)` using `(continuous_apply τ).comp hc`. Establish `hc2 : Continuous (fun z : Ker.powLat ΛM N N' => (z : n → Fin N' → Fin N → ℂ) τ k.1)` using `(continuous_apply k.1).comp hc1`. Conclude with `(continuous_apply k.2).comp hc2`. Establish `hψi : Function.Injective ψ`.

Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `τ i j`. Establish `h1` using `congrArg (fun f => ((f (i, j) : ΛM) : n → ℂ) τ) hxy`. Conclude with `h1`.

Conclude with `DiscreteTopology.of_continuous_injective hψc hψi`. Rewrite using `[eq_top_iff]`. Introduce `z _`. Rewrite using `[sum_putL N N' z]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations.

Establish `hk : (fun τ => z τ k.1 k.2) ∈ Submodule.span ℝ (ΛM : Set (n → ℂ))`. Rewrite using `[hs]`. Discharge the goal by the elementary cases of `trivial`. Establish `hmap : Submodule.map ((putL n N N' k).restrictScalars ℝ) (Submodule.span ℝ (ΛM : Set (n → ℂ))) ≤ Submodule.span ℝ (Ker.powLat ΛM N N' : Set _)`. Rewrite using `[Submodule.map_span]`.

Conclude with `Submodule.span_mono (by rintro _ ⟨y, hy, rfl⟩; exact putL_mem ΛM N N' k hy)`. Conclude with `hmap ⟨_, hk, rfl⟩`.
-/
theorem isLat_powLat (ΛM : AddSubgroup (n → ℂ)) (h : IsLat ΛM) (N N' : ℕ) : IsLat (Ker.powLat ΛM N N') := by
  obtain ⟨hd, hs⟩ := h
  refine ⟨?_, ?_⟩
  · haveI := hd
    let ψ : Ker.powLat ΛM N N' → (Fin N' × Fin N → ΛM) :=
      fun z k => ⟨fun τ => z.1 τ k.1 k.2, z.2 k.1 k.2⟩
    have hψc : Continuous ψ := by
      apply continuous_pi
      intro k
      apply Continuous.subtype_mk
      apply continuous_pi
      intro τ
      have hc : Continuous (fun z : Ker.powLat ΛM N N' => (z : n → Fin N' → Fin N → ℂ)) :=
        continuous_subtype_val
      have hc1 : Continuous (fun z : Ker.powLat ΛM N N' => (z : n → Fin N' → Fin N → ℂ) τ) :=
        (continuous_apply τ).comp hc
      have hc2 : Continuous (fun z : Ker.powLat ΛM N N' => (z : n → Fin N' → Fin N → ℂ) τ k.1) :=
        (continuous_apply k.1).comp hc1
      exact (continuous_apply k.2).comp hc2
    have hψi : Function.Injective ψ := by
      intro x y hxy
      apply Subtype.ext
      funext τ i j
      have h1 := congrArg (fun f => ((f (i, j) : ΛM) : n → ℂ) τ) hxy
      exact h1
    exact DiscreteTopology.of_continuous_injective hψc hψi
  · rw [eq_top_iff]
    intro z _
    rw [sum_putL N N' z]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hk : (fun τ => z τ k.1 k.2) ∈ Submodule.span ℝ (ΛM : Set (n → ℂ)) := by
      rw [hs]
      trivial
    have hmap : Submodule.map ((putL n N N' k).restrictScalars ℝ) (Submodule.span ℝ (ΛM : Set (n → ℂ))) ≤
        Submodule.span ℝ (Ker.powLat ΛM N N' : Set _) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono (by rintro _ ⟨y, hy, rfl⟩; exact putL_mem ΛM N N' k hy)
    exact hmap ⟨_, hk, rfl⟩

end Gen

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Cd.Base D cc δ}

/- English proof (translation)
Unfold `Formalism.L2.Ker.Cd.Base.StdOK Formalism.L2.Ker.StdOK at hS`. Establish `hI : IsLat (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))` using `Formalism.L2.Th1.H.KR.isLat_of_comm (Formalism.L2.Th1.H.KR.isLat_stdLat B.L _) hS.idx₂ hS.idx₁`. Conclude with `is_lattice_of_fourth_power B.lamM B.gC hI`.
-/
theorem isLat_lamM (hS : B.StdOK) : IsLat B.lamM := by
  unfold Formalism.L2.Ker.Cd.Base.StdOK Formalism.L2.Ker.StdOK at hS
  have hI : IsLat (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) :=
    Formalism.L2.Th1.H.KR.isLat_of_comm (Formalism.L2.Th1.H.KR.isLat_stdLat B.L _) hS.idx₂ hS.idx₁
  exact is_lattice_of_fourth_power B.lamM B.gC hI

/- English proof (translation)
Unfold `Lat0IsLat La0`. Rewrite using `[Formalism.L2.Ker.Cd.Lat0 (D := D) (N := N) (N' := N') cc δ]`. Conclude with `isLat_powLat _ (isLat_lamM hS) N N'`.
-/
theorem lat0IsLat (hS : B.StdOK) (N N' : ℕ) : Lat0IsLat B N N' := by
  unfold Lat0IsLat La0
  rw [Formalism.L2.Ker.Cd.Lat0 (D := D) (N := N) (N' := N') cc δ]
  exact isLat_powLat _ (isLat_lamM hS) N N'

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
