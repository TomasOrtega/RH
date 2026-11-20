import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirabolicEmbedding
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OpenSmooth

/- English proof (translation)
Set `T : Subgroup G` to `{ carrier := {g : G | ∀ m, F (m * g) = F m} mul_mem' := by`. Introduce `a b ha hb m`. Rewrite using `[← mul_assoc, hb, ha]`. Use the proof step `one_mem' := by intro m; rw [mul_one]`. Use the proof step `inv_mem' := by`.

Introduce `a ha m`. Use `ha (m * a⁻¹)` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_right]`. Conclude with `this.symm }`. Use `T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hN ?_)` and prove the remaining obligations.

Introduce `g hg`. Conclude with `h g hg`.
-/
theorem isOpen_rightPeriods {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (F : G → Z)
    (N : Set G) (hN : N ∈ nhds (1 : G)) (h : ∀ g ∈ N, ∀ m, F (m * g) = F m) :
    IsOpen {g : G | ∀ m, F (m * g) = F m} := by
  let T : Subgroup G :=
    { carrier := {g : G | ∀ m, F (m * g) = F m}
      mul_mem' := by
        intro a b ha hb m
        rw [← mul_assoc, hb, ha]
      one_mem' := by intro m; rw [mul_one]
      inv_mem' := by
        intro a ha m
        have := ha (m * a⁻¹)
        rw [inv_mul_cancel_right] at this
        exact this.symm }
  refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hN ?_)
  intro g hg
  exact h g hg

/- English proof (translation)
Establish `h : IsOpen {g : G | ind H σ g v.1 = v.1}` using `v.2`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Conclude with `Subtype.ext (funext hx)`. Introduce `hx y`. Conclude with `congrFun (congrArg Subtype.val hx) y`.
-/
theorem isOpen_stab_ind {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (v : smoothPart (ind H σ)) :
    IsOpen {x : G | ∀ y, v.1.1 (y * x) = v.1.1 y} := by
  have h : IsOpen {g : G | ind H σ g v.1 = v.1} := v.2
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    exact Subtype.ext (funext hx)
  · intro hx y
    exact congrFun (congrArg Subtype.val hx) y

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `continuous_id`.
-/
theorem continuous_castM {a b : ℕ} (h : a = b) : Continuous (castM k h) := by
  subst h
  exact continuous_id

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM k n`.
-/
theorem continuous_sEmb (n : ℕ) : Continuous (sEmb k n) :=
  GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM k n

/- English proof (translation)
The claim follows from `(GlobalTheory.CompanionTheory.LeibPhi.isOpen_ker_dpow k (n + 1) s).preimage continuous_subtype_val`.
-/
theorem isOpen_dpowM_eq_one (n : ℕ) (s : ℝ) : IsOpen {g : Mir k n | dpowM n s g = 1} :=
  (GlobalTheory.CompanionTheory.LeibPhi.isOpen_ker_dpow k (n + 1) s).preimage continuous_subtype_val

variable {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

/- English proof (translation)
Unfold `intO`. Use `congr 1`. Use function extensionality and compare the values at `d`. Rewrite using `[← mul_assoc]`. Conclude with `hκ _`.
-/
theorem intO_mul_of_stab (f : XS τ σ) (κ : Mir k ((i + 1) + t + 1))
    (hκ : ∀ x : Mir k ((i + 1) + (t + 1)), evX f (x * κ) = evX f x) (y : Mir k ((i + 1) + t + 1)) :
    intO f (y * κ) = intO f y := by
  unfold intO
  congr 1
  funext d
  rw [← mul_assoc]
  exact hκ _

/- English proof (translation)
Unfold `eO`. Rewrite using `[map_mul, hd, mul_one, map_mul, map_mul, ← mul_assoc, intO_mul_of_stab f _ hκ]`.
-/
theorem eO_mul_of_stab (ψ : AddChar k Circle) (f : XS τ σ) (m g : Mir k (i + (t + 1)))
    (hd : dpowM (i + (t + 1)) (-1 / 2) g = 1)
    (hκ : ∀ x : Mir k ((i + 1) + (t + 1)),
      evX f (x * sEmb k _ (castM k (by omega : i + (t + 1) = (i + 1) + t) g)) = evX f x) :
    eO ψ f (m * g) = eO ψ f m := by
  unfold eO
  rw [map_mul, hd, mul_one, map_mul, map_mul, ← mul_assoc, intO_mul_of_stab f _ hκ]

/- English proof (translation)
The claim follows from `isOpen_stab_ind _ _ (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ)))`.
-/
theorem isOpen_evX_stab (f : XS τ σ) :
    IsOpen {x : Mir k ((i + 1) + (t + 1)) | ∀ y : Mir k ((i + 1) + (t + 1)), evX f (y * x) = evX f y} :=
  isOpen_stab_ind _ _ (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ)))

end GlobalTheory.CompanionTheory.BZPhiPG.OpenSmooth

namespace GlobalTheory.CompanionTheory.BZPhiPG

open GlobalTheory.CompanionTheory.BZPhiPG.OpenSmooth in

/- English proof (translation)
Introduce `k _ _ _ _ i t ψ τ σ f`. Establish `hs : i + (t + 1) = (i + 1) + t` using `by omega`. Establish `hφ : Continuous fun g : Mir k (i + (t + 1)) => sEmb k _ (castM k hs g)` using `(continuous_sEmb _).comp (continuous_castM hs)`. Establish `hU : IsOpen ({g : Mir k (i + (t + 1)) | dpowM (i + (t + 1)) (-1 / 2) g = 1} ∩ (fun g : Mir k (i + (t + 1)) => sEmb k _ (castM k hs g)) ⁻¹' {x : Mir k ((i + 1) + (t + 1)) | ∀ y : Mir k ((i + 1) + (t + 1)), evX f (y * x) = evX f y})` using `(isOpen_dpowM_eq_one _ _).inter ((isOpen_evX_stab f).preimage hφ)`. Use `isOpen_rightPeriods (eO ψ f) _ (hU.mem_nhds ⟨map_one _, ?_⟩) ?_` and prove the remaining obligations.

Introduce `y`. Simplify using the standard rewrite rules. Introduce and unpack `g ⟨hd, hst⟩ m`. Conclude with `eO_mul_of_stab ψ f m g hd hst`.
-/
theorem isOpen_eO_rightPeriods : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ),
    IsOpen {g : Mir k (i + (t + 1)) | ∀ m, eO ψ f (m * g) = eO ψ f m} := by
  intro k _ _ _ _ i t ψ τ σ f
  have hs : i + (t + 1) = (i + 1) + t := by omega
  have hφ : Continuous fun g : Mir k (i + (t + 1)) => sEmb k _ (castM k hs g) :=
    (continuous_sEmb _).comp (continuous_castM hs)
  have hU : IsOpen ({g : Mir k (i + (t + 1)) | dpowM (i + (t + 1)) (-1 / 2) g = 1} ∩
      (fun g : Mir k (i + (t + 1)) => sEmb k _ (castM k hs g)) ⁻¹'
        {x : Mir k ((i + 1) + (t + 1)) | ∀ y : Mir k ((i + 1) + (t + 1)), evX f (y * x) = evX f y}) :=
    (isOpen_dpowM_eq_one _ _).inter ((isOpen_evX_stab f).preimage hφ)
  refine isOpen_rightPeriods (eO ψ f) _ (hU.mem_nhds ⟨map_one _, ?_⟩) ?_
  · intro y
    simp
  · rintro g ⟨hd, hst⟩ m
    exact eO_mul_of_stab ψ f m g hd hst

end GlobalTheory.CompanionTheory.BZPhiPG

end
