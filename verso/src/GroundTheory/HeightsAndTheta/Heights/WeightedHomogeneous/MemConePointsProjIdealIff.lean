import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] in

/- English proof (translation)
Establish `hw0 : BlockNonzero w ↔ w () ≠ 0` using `⟨fun h ↦ h (), fun h u ↦ by cases u; exact h⟩`. Set `σ : Fin (n k₀ + 1) → Coord (fun _ : Unit ↦ n k₀)` to `fun i ↦ ⟨(), i⟩`. Set `τ : Coord (fun _ : Unit ↦ n k₀) → Fin (n k₀ + 1)` to `fun v ↦ v.2`. Establish `hev : ∀ f, eval₂ (Int.castRingHom ℂ) (w ()) f = evalCone w (rename σ f)`. Introduce `f`.

Rewrite using `[evalCone, eval₂_rename]`. Both sides reduce to the same expression. Establish `hev' : ∀ f, evalCone w f = eval₂ (Int.castRingHom ℂ) (w ()) (rename τ f)`. Introduce `f`. Rewrite using `[evalCone, eval₂_rename]`.

Use `congr 1`. Simplify using `only [GroundTheory.Heights₂.Heights.conePoints, oneBlockPoints, Set.mem_ofPred_eq]`. Rewrite using `[hw0]`. Use `and_congr_right fun _ ↦ ⟨fun h f hf ↦ ?_, fun h f hf ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[hev]`.

Apply `h` to reduce the goal to its premises. Rewrite using `[ArithVariety.projIdeal, Ideal.mem_comap, rename_rename]`. Conclude with `Ideal.mem_comap.1 hf`. Rewrite using `[hev']`. Apply `h` to reduce the goal to its premises.

Rewrite using `[oneBlockIdeal, Ideal.mem_comap, rename_rename]`. Conclude with `Ideal.mem_comap.1 hf`.
-/
theorem mem_conePoints_projIdeal_iff (P : ArithVariety n) (k₀ : ι)
    (w : Cone (fun _ : Unit ↦ n k₀) ℂ) :
    w ∈ GroundTheory.Heights₂.Heights.conePoints (P.projIdeal k₀) ℂ ↔ w () ∈ oneBlockPoints P k₀ := by
  have hw0 : BlockNonzero w ↔ w () ≠ 0 := ⟨fun h ↦ h (), fun h u ↦ by cases u; exact h⟩
  let σ : Fin (n k₀ + 1) → Coord (fun _ : Unit ↦ n k₀) := fun i ↦ ⟨(), i⟩
  let τ : Coord (fun _ : Unit ↦ n k₀) → Fin (n k₀ + 1) := fun v ↦ v.2
  have hev : ∀ f, eval₂ (Int.castRingHom ℂ) (w ()) f = evalCone w (rename σ f) := by
    intro f
    rw [evalCone, eval₂_rename]
    rfl
  have hev' : ∀ f, evalCone w f = eval₂ (Int.castRingHom ℂ) (w ()) (rename τ f) := by
    intro f
    rw [evalCone, eval₂_rename]
    congr 1
  simp only [GroundTheory.Heights₂.Heights.conePoints, oneBlockPoints, Set.mem_ofPred_eq]
  rw [hw0]
  refine and_congr_right fun _ ↦ ⟨fun h f hf ↦ ?_, fun h f hf ↦ ?_⟩
  · rw [hev]
    apply h
    rw [ArithVariety.projIdeal, Ideal.mem_comap, rename_rename]
    exact Ideal.mem_comap.1 hf
  · rw [hev']
    apply h
    rw [oneBlockIdeal, Ideal.mem_comap, rename_rename]
    exact Ideal.mem_comap.1 hf

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h ι _ _ n P k₀`. Establish `hA` using `h ι n P k₀`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, hz, rfl⟩`. Establish `hz' : projBlock k₀ z ∈ GroundTheory.Heights₂.Heights.conePoints (P.projIdeal k₀) ℂ` using `hA ▸ ⟨z, hz, rfl⟩`. Conclude with `(mem_conePoints_projIdeal_iff P k₀ _).1 hz'`. Introduce `hv`. Establish `hv' : (fun _ : Unit ↦ v) ∈ GroundTheory.Heights₂.Heights.conePoints (P.projIdeal k₀) ℂ` using `(mem_conePoints_projIdeal_iff P k₀ _).2 hv`.

Rewrite `hv'` using `[← hA]`. Take `⟨z, hz, hzv⟩` from `hv'`. Conclude with `⟨z, hz, congrFun hzv ()⟩`. Introduce `h ι _ _ n P k₀`. Establish `hB` using `h ι n P k₀`.

Use extensionality with `w`. Rewrite using `[mem_conePoints_projIdeal_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `hB ▸ ⟨z, hz, rfl⟩`.

Introduce `hw`. Rewrite `hw` using `[← hB]`. Take `⟨z, hz, hzw⟩` from `hw`. Conclude with `⟨z, hz, funext fun u ↦ by cases u; exact hzw⟩`.
-/
theorem BlockSurjectivity.equiv :
    GroundTheory.Heights₂.Heights.BlockSurjectivity.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.BlockSurjectivity.Statement := by
  constructor
  · intro h ι _ _ n P k₀
    have hA := h ι n P k₀
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : projBlock k₀ z ∈ GroundTheory.Heights₂.Heights.conePoints (P.projIdeal k₀) ℂ :=
        hA ▸ ⟨z, hz, rfl⟩
      exact (mem_conePoints_projIdeal_iff P k₀ _).1 hz'
    · intro hv
      have hv' : (fun _ : Unit ↦ v) ∈ GroundTheory.Heights₂.Heights.conePoints (P.projIdeal k₀) ℂ :=
        (mem_conePoints_projIdeal_iff P k₀ _).2 hv
      rw [← hA] at hv'
      obtain ⟨z, hz, hzv⟩ := hv'
      exact ⟨z, hz, congrFun hzv ()⟩
  · intro h ι _ _ n P k₀
    have hB := h ι n P k₀
    ext w
    rw [mem_conePoints_projIdeal_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hB ▸ ⟨z, hz, rfl⟩
    · intro hw
      rw [← hB] at hw
      obtain ⟨z, hz, hzw⟩ := hw
      exact ⟨z, hz, funext fun u ↦ by cases u; exact hzw⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
