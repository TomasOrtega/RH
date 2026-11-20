import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.KerLat

variable {l : ℕ} [Fact l.Prime]

def kerMod {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) : Submodule ℤ_[l] (Fin d' → ℤ_[l]) where
  carrier := {v | ∀ i, (l : ℤ_[l]) ^ n ∣ (P *ᵥ v) i}
  add_mem' {a b} ha hb i := by
    rw [Matrix.mulVec_add]; exact dvd_add (ha i) (hb i)
  zero_mem' i := by simp
  smul_mem' c v hv i := by
    rw [Matrix.mulVec_smul]; exact Dvd.dvd.mul_left (hv i) c

/- English proof (translation)
Introduce `i`. Establish `e : P *ᵥ (A *ᵥ v) = (P * A - B * P) *ᵥ v + B *ᵥ (P *ᵥ v)`. Rewrite using `[Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, Pi.add_apply]`.

Use `dvd_add ?_ ?_` and prove the remaining obligations. Use `show _ ∣ ∑ j, (P * A - B * P) i j * v j`. Conclude with `Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (h i j) _`. Use `show _ ∣ ∑ j, B i j * (P *ᵥ v) j`. Conclude with `Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (hv j) _`.
-/
theorem mulVec_mem_kerMod {d d' n : ℕ} {P : Matrix (Fin d) (Fin d') ℤ_[l]}
    {A : Matrix (Fin d') (Fin d') ℤ_[l]} {B : Matrix (Fin d) (Fin d) ℤ_[l]}
    (h : ∀ i j, (l : ℤ_[l]) ^ n ∣ (P * A - B * P) i j) {v : Fin d' → ℤ_[l]} (hv : v ∈ kerMod P n) :
    A *ᵥ v ∈ kerMod P n := by
  intro i
  have e : P *ᵥ (A *ᵥ v) = (P * A - B * P) *ᵥ v + B *ᵥ (P *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; abel
  rw [e, Pi.add_apply]
  refine dvd_add ?_ ?_
  · show _ ∣ ∑ j, (P * A - B * P) i j * v j
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (h i j) _
  · show _ ∣ ∑ j, B i j * (P *ᵥ v) j
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (hv j) _

/- English proof (translation)
The claim follows from `pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)`.
-/
theorem pow_ne_zero' (n : ℕ) : ((l : ℤ_[l]) ^ n) ≠ 0 :=
  pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hm : ∀ v : Fin d' → ℤ_[l], ((l : ℤ_[l]) ^ n • LinearMap.id : (Fin d' → ℤ_[l]) →ₗ[ℤ_[l]] _) v ∈ kerMod P n`. Introduce `v i`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]`.

Conclude with `dvd_mul_right _ _`. Set `φ : (Fin d' → ℤ_[l]) →ₗ[ℤ_[l]] kerMod P n` to `LinearMap.codRestrict (kerMod P n) ((l : ℤ_[l]) ^ n • LinearMap.id) hm`. Establish `hinj : Function.Injective φ`. Introduce `a b hab`. Establish `h2` using `congrArg Subtype.val hab`.

Simplify using `only [φ, LinearMap.codRestrict_apply, LinearMap.smul_apply, LinearMap.id_apply] at h2`. Conclude with `smul_right_injective _ (pow_ne_zero' n) h2`. Use `LinearMap.finrank_le_finrank_of_injective hinj` as an intermediate fact. Simplify using `using this`.
-/
theorem finrank_kerMod {d d' n : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) :
    Module.finrank ℤ_[l] (kerMod P n) = d' := by
  apply le_antisymm
  · calc Module.finrank ℤ_[l] (kerMod P n) ≤ Module.finrank ℤ_[l] (Fin d' → ℤ_[l]) :=
          Submodule.finrank_le _
      _ = d' := by simp
  · have hm : ∀ v : Fin d' → ℤ_[l], ((l : ℤ_[l]) ^ n • LinearMap.id : (Fin d' → ℤ_[l]) →ₗ[ℤ_[l]] _) v ∈ kerMod P n := by
      intro v i
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    let φ : (Fin d' → ℤ_[l]) →ₗ[ℤ_[l]] kerMod P n :=
      LinearMap.codRestrict (kerMod P n) ((l : ℤ_[l]) ^ n • LinearMap.id) hm
    have hinj : Function.Injective φ := by
      intro a b hab
      have h2 := congrArg Subtype.val hab
      simp only [φ, LinearMap.codRestrict_apply, LinearMap.smul_apply, LinearMap.id_apply] at h2
      exact smul_right_injective _ (pow_ne_zero' n) h2
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this

end GlobalTheory.KerLat

namespace GlobalTheory.KerLat

variable {l : ℕ} [Fact l.Prime]

noncomputable def kerBasis {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) :
    Module.Basis (Fin d') ℤ_[l] (kerMod P n) :=
  Module.finBasisOfFinrankEq ℤ_[l] (kerMod P n) (finrank_kerMod P)

noncomputable def kerMat {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) :
    Matrix (Fin d') (Fin d') ℤ_[l] :=
  Matrix.of fun i j => ((kerBasis P n j : kerMod P n) : Fin d' → ℤ_[l]) i

/- English proof (translation)
Use extensionality with `i`. Simplify using `[kerMat, Matrix.mulVec, dotProduct, Submodule.coe_sum, Finset.sum_apply, mul_comm]`.
-/
theorem kerMat_mulVec {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) (w : Fin d' → ℤ_[l]) :
    kerMat P n *ᵥ w = ((∑ j, w j • kerBasis P n j : kerMod P n) : Fin d' → ℤ_[l]) := by
  ext i
  simp [kerMat, Matrix.mulVec, dotProduct, Submodule.coe_sum, Finset.sum_apply, mul_comm]

/- English proof (translation)
Introduce `l _ Γ _ d d' n ρ ρ' P hP`. Use `set b := kerBasis P n`. Use `set f := kerMat P n`. Establish `hf : ∀ w, f *ᵥ w = ((∑ j, w j • b j : kerMod P n) : Fin d' → ℤ_[l])` using `kerMat_mulVec P n`. Establish `hiff : ∀ v, v ∈ kerMod P n ↔ ∃ w, v = f *ᵥ w`.

Introduce `v`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Use `⟨b.repr ⟨v, hv⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, b.sum_repr]`.

Introduce and unpack `⟨w, rfl⟩`. Rewrite using `[hf]`. Conclude with `Submodule.coe_mem _`. Establish `hinj : ∀ w, f *ᵥ w = 0 → w = 0`. Introduce `w hw`.

Rewrite `hw` using `[hf]`. Establish `h0 : (∑ j, w j • b j) = 0` using `Subtype.ext hw`. Use function extensionality and compare the values at `j`. Conclude with `Fintype.linearIndependent_iff.mp b.linearIndependent w h0 j`. Establish `hdet : f.det ≠ 0`.

Introduce `h0`. Take `⟨w, hw0, hw⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Conclude with `hw0 (hinj w hw)`. Establish `hcancel : ∀ X Y : Matrix (Fin d') (Fin d') ℤ_[l], f * X = f * Y → X = Y`. Introduce `X Y h`.

Establish `h2` using `congrArg (fun M => f.adjugate * M) h`. Simplify using `only [← Matrix.mul_assoc, Matrix.adjugate_mul] at h2`. Use extensionality with `i j`. Establish `h3` using `congrFun (congrFun h2 i) j`. Simplify using `only [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul] at h3`.

Conclude with `mul_left_cancel₀ hdet h3`. Establish `hcol : ∀ g j, ∃ w, (ρ' g).val *ᵥ (fun i => f i j) = f *ᵥ w`. Introduce `g j`. Apply `(hiff _).mp` to reduce the goal to its premises. Apply `mulVec_mem_kerMod (A := (ρ' g).val) (B := (ρ g).val) (hP.equi g)` to reduce the goal to its premises.

Conclude with `Submodule.coe_mem (b j)`. Use `choose W hW using hcol`. Set `R : Γ → Matrix (Fin d') (Fin d') ℤ_[l]` to `fun g => Matrix.of fun i j => W g j i`. Establish `hR : ∀ g, f * R g = (ρ' g).val * f`. Introduce `g`.

Use extensionality with `i j`. Use `congrFun (hW g j) i` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct] at this`. Simplify using `only [Matrix.mul_apply, R, Matrix.of_apply]`. Conclude with `this.symm`.

Establish `hR1 : R 1 = 1` using `hcancel _ _ (by rw [hR, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])`. Establish `hRm : ∀ g h, R (g * h) = R g * R h` using `fun g h => hcancel _ _ (by`. Rewrite using `[hR, map_mul, Units.val_mul, Matrix.mul_assoc, ← hR h, ← Matrix.mul_assoc, ← hR g, Matrix.mul_assoc])`. Set `Rm : Γ →* Matrix (Fin d') (Fin d') ℤ_[l]` to `{ toFun := R, map_one' := hR1, map_mul' := hRm }`. Use `⟨f, Rm.toHomUnits, hdet, fun g => hR g, fun v => hiff v⟩` and prove the remaining obligations.
-/
theorem exists_kernel_lattice : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (d d' n : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])), Onto (fun g => (ρ g).val) (fun g => (ρ' g).val) Pi n → ∃ (f : Matrix (Fin d') (Fin d') (ℤ_[l])) (ρ'' : Γ →* GL (Fin d') ℤ_[l]), f.det ≠ 0 ∧ (∀ g, f * (ρ'' g).val = (ρ' g).val * f) ∧ ∀ v : Fin d' → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ (Pi *ᵥ v) i) ↔ ∃ w, v = f *ᵥ w := by
  intro l _ Γ _ d d' n ρ ρ' P hP
  set b := kerBasis P n
  set f := kerMat P n
  have hf : ∀ w, f *ᵥ w = ((∑ j, w j • b j : kerMod P n) : Fin d' → ℤ_[l]) := kerMat_mulVec P n
  have hiff : ∀ v, v ∈ kerMod P n ↔ ∃ w, v = f *ᵥ w := by
    intro v; constructor
    · intro hv; refine ⟨b.repr ⟨v, hv⟩, ?_⟩
      rw [hf, b.sum_repr]
    · rintro ⟨w, rfl⟩; rw [hf]; exact Submodule.coe_mem _
  have hinj : ∀ w, f *ᵥ w = 0 → w = 0 := by
    intro w hw
    rw [hf] at hw
    have h0 : (∑ j, w j • b j) = 0 := Subtype.ext hw
    funext j
    exact Fintype.linearIndependent_iff.mp b.linearIndependent w h0 j
  have hdet : f.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hw0 (hinj w hw)
  have hcancel : ∀ X Y : Matrix (Fin d') (Fin d') ℤ_[l], f * X = f * Y → X = Y := by
    intro X Y h
    have h2 := congrArg (fun M => f.adjugate * M) h
    simp only [← Matrix.mul_assoc, Matrix.adjugate_mul] at h2
    ext i j
    have h3 := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul] at h3
    exact mul_left_cancel₀ hdet h3
  have hcol : ∀ g j, ∃ w, (ρ' g).val *ᵥ (fun i => f i j) = f *ᵥ w := by
    intro g j
    apply (hiff _).mp
    apply mulVec_mem_kerMod (A := (ρ' g).val) (B := (ρ g).val) (hP.equi g)
    exact Submodule.coe_mem (b j)
  choose W hW using hcol
  let R : Γ → Matrix (Fin d') (Fin d') ℤ_[l] := fun g => Matrix.of fun i j => W g j i
  have hR : ∀ g, f * R g = (ρ' g).val * f := by
    intro g; ext i j
    have := congrFun (hW g j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, R, Matrix.of_apply]
    exact this.symm
  have hR1 : R 1 = 1 := hcancel _ _ (by rw [hR, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
  have hRm : ∀ g h, R (g * h) = R g * R h := fun g h => hcancel _ _ (by
    rw [hR, map_mul, Units.val_mul, Matrix.mul_assoc, ← hR h, ← Matrix.mul_assoc, ← hR g, Matrix.mul_assoc])
  let Rm : Γ →* Matrix (Fin d') (Fin d') ℤ_[l] := { toFun := R, map_one' := hR1, map_mul' := hRm }
  refine ⟨f, Rm.toHomUnits, hdet, fun g => hR g, fun v => hiff v⟩

end GlobalTheory.KerLat
