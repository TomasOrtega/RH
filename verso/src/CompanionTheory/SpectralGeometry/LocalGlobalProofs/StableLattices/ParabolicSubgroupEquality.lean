import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts

noncomputable section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.PSubFlag

open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S GlobalTheory.FlagMeas Formalism.MainNotions.S

variable {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}

def Pm (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A - A)

def Pp (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A + A)

/- English proof (translation)
Simplify using `only [Vm, LinearMap.mem_range, Matrix.toLin'_apply, Pm]`.
-/
theorem mem_Vm {x : Fin n → ℂ} : x ∈ Vm A ↔ ∃ z, Pm A *ᵥ z = x := by
  simp only [Vm, LinearMap.mem_range, Matrix.toLin'_apply, Pm]

/- English proof (translation)
Simplify using `only [Wm, LinearMap.mem_ker, Matrix.toLin'_apply, Pp]`.
-/
theorem mem_Wm {y : Fin n → ℂ} : y ∈ Wm A ↔ Pp A *ᵥ y = 0 := by
  simp only [Wm, LinearMap.mem_ker, Matrix.toLin'_apply, Pp]

/- English proof (translation)
Establish `h` using `hA.1`. Unfold `Formalism.REAL.inG at h`. Rewrite `h` using `[hA.2.1]`. Conclude with `eq_neg_of_add_eq_zero_right h`.
-/
theorem anti (hA : IsGrad ε A) : Formalism.REAL.Jm ε * A = -(A * Formalism.REAL.Jm ε) := by
  have h := hA.1
  unfold Formalism.REAL.inG at h
  rw [hA.2.1] at h
  exact eq_neg_of_add_eq_zero_right h

/- English proof (translation)
Simplify using `[Pm, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hA.2.1]`.
-/
theorem Pm_conj (hA : IsGrad ε A) : (Pm A)ᴴ = Pm A := by
  simp [Pm, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hA.2.1]

/- English proof (translation)
Establish `h` using `anti hA`. Establish `h2 : Formalism.REAL.Jm ε * (A * A) = A * A * Formalism.REAL.Jm ε`. Rewrite using `[← Matrix.mul_assoc, h, Matrix.neg_mul, Matrix.mul_assoc, h, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]`. Simplify using `only [Pm, Pp, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h, h2, sub_eq_add_neg, Matrix.neg_mul]`.
-/
theorem Pm_J (hA : IsGrad ε A) : Pm A * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Pp A := by
  have h := anti hA
  have h2 : Formalism.REAL.Jm ε * (A * A) = A * A * Formalism.REAL.Jm ε := by
    rw [← Matrix.mul_assoc, h, Matrix.neg_mul, Matrix.mul_assoc, h, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  simp only [Pm, Pp, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h, h2, sub_eq_add_neg, Matrix.neg_mul]

/- English proof (translation)
Establish `h` using `hA.2.2.1`. Establish `e : (A * A + A) * (A * A - A) = 0`. Establish `: (A * A + A) * (A * A - A) = (A * A * A) * A - A * A`. Simplify using `only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws.

Rewrite using `[this, h, sub_self]`. Simplify using `only [Pp, Pm, Matrix.smul_mul, Matrix.mul_smul, e, smul_zero]`.
-/
theorem Pp_Pm (hA : IsGrad ε A) : Pp A * Pm A = 0 := by
  have h := hA.2.2.1
  have e : (A * A + A) * (A * A - A) = 0 := by
    have : (A * A + A) * (A * A - A) = (A * A * A) * A - A * A := by
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [this, h, sub_self]
  simp only [Pp, Pm, Matrix.smul_mul, Matrix.mul_smul, e, smul_zero]

/- English proof (translation)
Introduce `x hx`. Take `⟨z, rfl⟩` from `mem_Vm.1 hx`. Rewrite using `[mem_Wm, Matrix.mulVec_mulVec, Pp_Pm hA, Matrix.zero_mulVec]`.
-/
theorem Vm_le_Wm (hA : IsGrad ε A) : Vm A ≤ Wm A := by
  intro x hx
  obtain ⟨z, rfl⟩ := mem_Vm.1 hx
  rw [mem_Wm, Matrix.mulVec_mulVec, Pp_Pm hA, Matrix.zero_mulVec]

/- English proof (translation)
Establish `key : ∀ z, star (Pm A *ᵥ z) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = star z ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (Pp A *ᵥ y))`. Introduce `z`. Rewrite using `[Matrix.star_mulVec, Pm_conj hA, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Pm_J hA, Matrix.mulVec_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce `hy x hx`.

Take `⟨z, rfl⟩` from `mem_Vm.1 hx`. Rewrite using `[key, mem_Wm.1 hy, Matrix.mulVec_zero, dotProduct_zero]`. Introduce `h`. Establish `h1` using `h _ (mem_Vm.2 ⟨Formalism.REAL.Jm ε *ᵥ (Pp A *ᵥ y), rfl⟩)`. Rewrite `h1` using `[key, dotProduct_star_self_eq_zero]`.

Establish `h2` using `congrArg (Formalism.REAL.Jm ε *ᵥ ·) h1`. Simplify using `only [Matrix.mulVec_mulVec, Formalism.REAL.Jm_mul_self, ← Matrix.mul_assoc, Matrix.one_mul, Matrix.mulVec_zero] at h2`. Conclude with `mem_Wm.2 h2`.
-/
theorem mem_Wm_iff (hA : IsGrad ε A) (y : Fin n → ℂ) :
    y ∈ Wm A ↔ ∀ x ∈ Vm A, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
  have key : ∀ z, star (Pm A *ᵥ z) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = star z ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (Pp A *ᵥ y)) := by
    intro z
    rw [Matrix.star_mulVec, Pm_conj hA, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Pm_J hA,
      Matrix.mulVec_mulVec]
  constructor
  · intro hy x hx
    obtain ⟨z, rfl⟩ := mem_Vm.1 hx
    rw [key, mem_Wm.1 hy, Matrix.mulVec_zero, dotProduct_zero]
  · intro h
    have h1 := h _ (mem_Vm.2 ⟨Formalism.REAL.Jm ε *ᵥ (Pp A *ᵥ y), rfl⟩)
    rw [key, dotProduct_star_self_eq_zero] at h1
    have h2 := congrArg (Formalism.REAL.Jm ε *ᵥ ·) h1
    simp only [Matrix.mulVec_mulVec, Formalism.REAL.Jm_mul_self, ← Matrix.mul_assoc, Matrix.one_mul, Matrix.mulVec_zero] at h2
    exact mem_Wm.2 h2

/- English proof (translation)
Use `⟨rfl, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `intro i k h fin_cases i <;> fin_cases k <;> simp_all [W]`. Introduce `i fin_cases i show Module.finrank ℂ (Vm A) = Module.finrank ℂ (⊥ : Submodule ℂ (Fin n → ℂ)) + rk A`. Simplify using `[rk]`. Introduce `x hx y hy`.

Conclude with `(mem_Wm_iff hA y).1 (Vm_le_Wm hA hy) x hx`.
-/
theorem isoFlag (hA : IsGrad ε A) : IsIsoFlag ε (fun _ : Fin 1 => rk A) (W A) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i k h
    fin_cases i <;> fin_cases k <;> simp_all [W]
  · intro i
    fin_cases i
    show Module.finrank ℂ (Vm A) = Module.finrank ℂ (⊥ : Submodule ℂ (Fin n → ℂ)) + rk A
    simp [rk]
  · intro x hx y hy
    exact (mem_Wm_iff hA y).1 (Vm_le_Wm hA hy) x hx

/- English proof (translation)
The claim follows from `Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨y, hy, rfl⟩; exact h y hy) (GlobalTheory.RealIwasawa.finrank_map_toLin _ _ (GlobalTheory.RealIwasawa.uMat_inv_mul g) S)`.
-/
theorem keeps_of_stable (g : Formalism.REAL.UJ ε) {S : Submodule ℂ (Fin n → ℂ)} (h : ∀ y ∈ S, uMat g *ᵥ y ∈ S) :
    Keeps (uMat g) S :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)
    (GlobalTheory.RealIwasawa.finrank_map_toLin _ _ (GlobalTheory.RealIwasawa.uMat_inv_mul g) S)

/- English proof (translation)
Introduce `y hy` and use `by have : Matrix.toLin' g y ∈ S.map (Matrix.toLin' g) := Submodule.mem_map_of_mem hy rw [h, Matrix.toLin'_apply] at this exact this`.
-/
theorem stable_of_keeps {g : Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℂ (Fin n → ℂ)} (h : Keeps g S) :
    ∀ y ∈ S, g *ᵥ y ∈ S := fun y hy => by
  have : Matrix.toLin' g y ∈ S.map (Matrix.toLin' g) := Submodule.mem_map_of_mem hy
  rw [h, Matrix.toLin'_apply] at this
  exact this

/- English proof (translation)
Establish `h : uMat u *ᵥ y - y ∈ (⊥ : Submodule ℂ (Fin n → ℂ))` using `hu.1 0 y hy`. Conclude with `sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 h)`.
-/
theorem flagN_fix {u : Formalism.REAL.UJ ε} (hu : u ∈ flagN ε (W A)) {y : Fin n → ℂ} (hy : y ∈ Vm A) :
    uMat u *ᵥ y = y := by
  have h : uMat u *ᵥ y - y ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := hu.1 0 y hy
  exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 h)

/- English proof (translation)
Establish `h : uMat u *ᵥ y - y ∈ Vm A` using `hu.2 y ((mem_Wm_iff hA y).1 hy)`. Use `add_mem (Vm_le_Wm hA h) hy` as an intermediate fact. Simplify using `using this`.
-/
theorem flagN_stable_Wm (hA : IsGrad ε A) {u : Formalism.REAL.UJ ε} (hu : u ∈ flagN ε (W A)) {y : Fin n → ℂ}
    (hy : y ∈ Wm A) : uMat u *ᵥ y ∈ Wm A := by
  have h : uMat u *ᵥ y - y ∈ Vm A := hu.2 y ((mem_Wm_iff hA y).1 hy)
  have := add_mem (Vm_le_Wm hA h) hy
  simpa using this

/- English proof (translation)
The claim follows from `(hm 1 y hy).1`.
-/
theorem flagM_stable_Vm {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) {y : Fin n → ℂ} (hy : y ∈ Vm A) :
    uMat m *ᵥ y ∈ Vm A :=
  (hm 1 y hy).1

/- English proof (translation)
Use `(mem_Wm_iff hA _).2 fun x hx => ?_` and prove the remaining obligations. Establish `hx' : uMat m⁻¹ *ᵥ x ∈ Vm A` using `GlobalTheory.RealIwasawa.inv_stable _ _ (GlobalTheory.RealIwasawa.uMat_inv_mul m) (Vm A) (fun z hz => flagM_stable_Vm hm hz) x hx`. Establish `e : x = uMat m *ᵥ (uMat m⁻¹ *ᵥ x)`. Rewrite using `[Matrix.mulVec_mulVec, GlobalTheory.RealIwasawa.uMat_mul_inv, Matrix.one_mulVec]`. Establish `h0` using `(mem_Wm_iff hA y).1 hy _ hx'`.

Rewrite using `[e, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, GlobalTheory.RealIwasawa.uMat_form]`. Conclude with `h0`.
-/
theorem flagM_stable_Wm (hA : IsGrad ε A) {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) {y : Fin n → ℂ}
    (hy : y ∈ Wm A) : uMat m *ᵥ y ∈ Wm A := by
  refine (mem_Wm_iff hA _).2 fun x hx => ?_
  have hx' : uMat m⁻¹ *ᵥ x ∈ Vm A :=
    GlobalTheory.RealIwasawa.inv_stable _ _ (GlobalTheory.RealIwasawa.uMat_inv_mul m) (Vm A)
      (fun z hz => flagM_stable_Vm hm hz) x hx
  have e : x = uMat m *ᵥ (uMat m⁻¹ *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, GlobalTheory.RealIwasawa.uMat_mul_inv, Matrix.one_mulVec]
  have h0 := (mem_Wm_iff hA y).1 hy _ hx'
  rw [e, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    GlobalTheory.RealIwasawa.uMat_form]
  exact h0

/- English proof (translation)
Introduce `n ε A hA g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `hp : ∀ i, ∀ y ∈ W A i, uMat g *ᵥ y ∈ W A i`. Introduce `i y hy`.

Use `fin_cases i`. Establish `: y = 0` using `(Submodule.mem_bot ℂ).1 hy`. Rewrite using `[this, Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Conclude with `stable_of_keeps hg.1 y hy`.

Take `⟨m, hm, hu⟩` from `GlobalTheory.RealIwasawa.exists_unip_mul_levi (isoFlag hA) g hp`. Conclude with `⟨g * m⁻¹, hu, m, hm, by group⟩`. Introduce and unpack `⟨u, hu, m, hm, rfl⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `keeps_mul (keeps_of_stable u fun y hy => by rw [flagN_fix hu hy]; exact hy) (keeps_of_stable m fun y hy => flagM_stable_Vm hm hy)`.

Conclude with `keeps_mul (keeps_of_stable u fun y hy => flagN_stable_Wm hA hu hy) (keeps_of_stable m fun y hy => flagM_stable_Wm hA hm hy)`.
-/
theorem psubEq : PSubEq := by
  intro n ε A hA g
  constructor
  · intro hg
    have hp : ∀ i, ∀ y ∈ W A i, uMat g *ᵥ y ∈ W A i := by
      intro i y hy
      fin_cases i
      · have : y = 0 := (Submodule.mem_bot ℂ).1 hy
        rw [this, Matrix.mulVec_zero]
        exact zero_mem _
      · exact stable_of_keeps hg.1 y hy
    obtain ⟨m, hm, hu⟩ := GlobalTheory.RealIwasawa.exists_unip_mul_levi (isoFlag hA) g hp
    exact ⟨g * m⁻¹, hu, m, hm, by group⟩
  · rintro ⟨u, hu, m, hm, rfl⟩
    refine ⟨?_, ?_⟩
    · exact keeps_mul (keeps_of_stable u fun y hy => by rw [flagN_fix hu hy]; exact hy)
        (keeps_of_stable m fun y hy => flagM_stable_Vm hm hy)
    · exact keeps_mul (keeps_of_stable u fun y hy => flagN_stable_Wm hA hu hy)
        (keeps_of_stable m fun y hy => flagM_stable_Wm hA hm hy)

end GlobalTheory.CompanionTheory.PSubFlag
