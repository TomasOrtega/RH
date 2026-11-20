import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarAction

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.PartShift

section Abstract

variable {O : Type} [CommRing O] {K : Type} [CommRing K] [Algebra O K]
  {Γ Λ : Type} [CommRing Γ] [CommRing Λ] {h h' : ℕ}
  {ρ : Γ → Matrix (Fin h) (Fin h) O} {ρ' : Λ → Matrix (Fin h') (Fin h') O}
  {π : Γ →+* Λ} {e : Γ} {P : Matrix (Fin h') (Fin h) O} {I : Matrix (Fin h) (Fin h') O}

/- English proof (translation)
Take `⟨x, rfl⟩` from `hπ a`. Establish `hIPk : I.map (algebraMap O K) * P.map (algebraMap O K) = (ρ e).map (algebraMap O K)`. Rewrite using `[← Matrix.map_mul, hIP]`. Establish `hev : (ρ e).map (algebraMap O K) *ᵥ v = v` using `by rw [hv, he, map_one, map_one, one_smul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hact]`. Simplify using `only [Matrix.map_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Use `_ = _ := by rw [hIPk, hev, hv, Matrix.mulVec_smul]`.
-/
theorem mulVec_mem_eigenspace (hIP : I * P = ρ e) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (hπ : Function.Surjective π) (he : π e = 1) (σ : Λ →+* O) (v : Fin h → K)
    (hv : ∀ a, (ρ a).map (algebraMap O K) *ᵥ v = algebraMap O K (σ (π a)) • v) (a : Λ) :
    (ρ' a).map (algebraMap O K) *ᵥ (P.map (algebraMap O K) *ᵥ v) =
      algebraMap O K (σ a) • (P.map (algebraMap O K) *ᵥ v) := by
  obtain ⟨x, rfl⟩ := hπ a
  have hIPk : I.map (algebraMap O K) * P.map (algebraMap O K) = (ρ e).map (algebraMap O K) := by
    rw [← Matrix.map_mul, hIP]
  have hev : (ρ e).map (algebraMap O K) *ᵥ v = v := by rw [hv, he, map_one, map_one, one_smul]
  calc (ρ' (π x)).map (algebraMap O K) *ᵥ (P.map (algebraMap O K) *ᵥ v)
      = P.map (algebraMap O K) *ᵥ ((ρ x).map (algebraMap O K) *ᵥ
          ((I.map (algebraMap O K) * P.map (algebraMap O K)) *ᵥ v)) := by
        rw [hact]; simp only [Matrix.map_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = _ := by rw [hIPk, hev, hv, Matrix.mulVec_smul]

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.map_mul, hIP, hv, he, map_one, map_one, one_smul]`.
-/
theorem mulVec_mulVec_eq_self_of_eigenvector (hIP : I * P = ρ e) (he : π e = 1) (σ : Λ →+* O) (v : Fin h → K)
    (hv : ∀ a, (ρ a).map (algebraMap O K) *ᵥ v = algebraMap O K (σ (π a)) • v) :
    I.map (algebraMap O K) *ᵥ (P.map (algebraMap O K) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hIP, hv, he, map_one, map_one, one_smul]

/- English proof (translation)
Establish `key : ρ x * I = I * (P * ρ x * I)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.map_mul, key, ← hact, Matrix.map_mul, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]`.
-/
theorem I_eigen (hPI : P * I = 1) (hIP : I * P = ρ e)
    (hcomm : ∀ x, ρ x * ρ e = ρ e * ρ x) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (τ : Λ →+* O) (w : Fin h' → K)
    (hw : ∀ a, (ρ' a).map (algebraMap O K) *ᵥ w = algebraMap O K (τ a) • w) (x : Γ) :
    (ρ x).map (algebraMap O K) *ᵥ (I.map (algebraMap O K) *ᵥ w) =
      algebraMap O K (τ (π x)) • (I.map (algebraMap O K) *ᵥ w) := by
  have key : ρ x * I = I * (P * ρ x * I) := by
    calc ρ x * I = ρ x * (I * P * I) := by rw [Matrix.mul_assoc, hPI, Matrix.mul_one]
      _ = (ρ x * ρ e) * I := by rw [hIP, Matrix.mul_assoc]
      _ = (ρ e * ρ x) * I := by rw [hcomm]
      _ = I * (P * ρ x * I) := by rw [← hIP]; simp only [Matrix.mul_assoc]
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, key, ← hact, Matrix.map_mul, ← Matrix.mulVec_mulVec,
    hw, Matrix.mulVec_smul]

end Abstract

end GlobalTheory.DetInv.PartShift

namespace GlobalTheory.DetInv.PartShift

section EigC

variable {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C]
  {Γ Λ : Type} [CommRing Γ] [CommRing Λ] {h h' : ℕ}
  {ρ : Γ → Matrix (Fin h) (Fin h) O} {ρ' : Λ → Matrix (Fin h') (Fin h') O}
  {π : Γ →+* Λ} {e : Γ} {P : Matrix (Fin h') (Fin h) O} {I : Matrix (Fin h) (Fin h') O}

/- English proof (translation)
Simplify using `[eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]`.
-/
theorem mem_eig_iff {n : ℕ} {Δ : Type} [CommRing Δ] (ρ₀ : Δ → Matrix (Fin n) (Fin n) O)
    (σ : Δ →+* O) (v : Fin n → C) :
    v ∈ eig C ρ₀ σ ↔ ∀ a, (ρ₀ a).map (algebraMap O C) *ᵥ v = algebraMap O C (σ a) • v := by
  simp [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

/- English proof (translation)
Rewrite `hv`, the goal using `[mem_eig_iff]`. Introduce `a`. Rewrite using `[Matrix.toLin'_apply]`. Conclude with `mulVec_mem_eigenspace hIP hact hπ he σ v (fun a => hv a) a`.
-/
theorem eig_P (hIP : I * P = ρ e) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (hπ : Function.Surjective π) (he : π e = 1) (σ : Λ →+* O) {v : Fin h → C}
    (hv : v ∈ eig C ρ (σ.comp π)) : Matrix.toLin' (P.map (algebraMap O C)) v ∈ eig C ρ' σ := by
  rw [mem_eig_iff] at hv ⊢
  intro a
  rw [Matrix.toLin'_apply]
  exact mulVec_mem_eigenspace hIP hact hπ he σ v (fun a => hv a) a

/- English proof (translation)
Rewrite `hv` using `[mem_eig_iff]`. Simplify using `only [Matrix.toLin'_apply]`. Conclude with `mulVec_mulVec_eq_self_of_eigenvector hIP he σ v (fun a => hv a)`.
-/
theorem eig_IP (hIP : I * P = ρ e) (he : π e = 1) (σ : Λ →+* O) {v : Fin h → C}
    (hv : v ∈ eig C ρ (σ.comp π)) :
    Matrix.toLin' (I.map (algebraMap O C)) (Matrix.toLin' (P.map (algebraMap O C)) v) = v := by
  rw [mem_eig_iff] at hv
  simp only [Matrix.toLin'_apply]
  exact mulVec_mulVec_eq_self_of_eigenvector hIP he σ v (fun a => hv a)

/- English proof (translation)
Rewrite `hw`, the goal using `[mem_eig_iff]`. Introduce `x`. Rewrite using `[Matrix.toLin'_apply]`. Conclude with `I_eigen hPI hIP hcomm hact τ w hw x`.
-/
theorem eig_I (hPI : P * I = 1) (hIP : I * P = ρ e)
    (hcomm : ∀ x, ρ x * ρ e = ρ e * ρ x) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (τ : Λ →+* O) {w : Fin h' → C} (hw : w ∈ eig C ρ' τ) :
    Matrix.toLin' (I.map (algebraMap O C)) w ∈ eig C ρ (τ.comp π) := by
  rw [mem_eig_iff] at hw ⊢
  intro x
  rw [Matrix.toLin'_apply]
  exact I_eigen hPI hIP hcomm hact τ w hw x

/- English proof (translation)
Simplify using `only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, hPI, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]`.
-/
theorem eig_PI (hPI : P * I = 1) (w : Fin h' → C) :
    Matrix.toLin' (P.map (algebraMap O C)) (Matrix.toLin' (I.map (algebraMap O C)) w) = w := by
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, hPI,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

/- English proof (translation)
Establish `hidem : IsIdempotentElem (algebraMap O C (σ e))`. Unfold `IsIdempotentElem`. Rewrite using `[← map_mul, ← map_mul, he2.eq]`. Break down `(IsIdempotentElem.iff_eq_zero_or_one.mp hidem) with h0 | h1` into its components or cases. Use `left`.

Rewrite `hv` using `[mem_eig_iff]`. Establish `hP : P = P * ρ e` using `by rw [← hIP, ← Matrix.mul_assoc, hPI, Matrix.one_mul]`. Rewrite using `[Matrix.toLin'_apply, hP, Matrix.map_mul, ← Matrix.mulVec_mulVec, hv, h0, zero_smul, Matrix.mulVec_zero]`. Use `right`. Establish `hσe : σ e = 1` using `hinj (by rw [h1, map_one])`.

Establish `hle : RingHom.ker π ≤ RingHom.ker σ`. Rewrite using `[hker, Ideal.span_le, Set.singleton_subset_iff]`. Simplify using `[RingHom.mem_ker, map_sub, hσe]`. Use `⟨π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ) ⟨σ, hle⟩, ?_⟩` and prove the remaining obligations. Conclude with `(RingHom.liftOfRightInverse_comp π _ _ ⟨σ, hle⟩).symm`.
-/
theorem eq_zero_or_factors_of_mem_eigenspace (hPI : P * I = 1) (hIP : I * P = ρ e) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = Ideal.span {1 - e})
    (hinj : Function.Injective (algebraMap O C)) (he2 : IsIdempotentElem e)
    (σ : Γ →+* O) {v : Fin h → C} (hv : v ∈ eig C ρ σ) :
    Matrix.toLin' (P.map (algebraMap O C)) v = 0 ∨ ∃ σ' : Λ →+* O, σ = σ'.comp π := by
  have hidem : IsIdempotentElem (algebraMap O C (σ e)) := by
    unfold IsIdempotentElem; rw [← map_mul, ← map_mul, he2.eq]
  rcases (IsIdempotentElem.iff_eq_zero_or_one.mp hidem) with h0 | h1
  · left
    rw [mem_eig_iff] at hv
    have hP : P = P * ρ e := by rw [← hIP, ← Matrix.mul_assoc, hPI, Matrix.one_mul]
    rw [Matrix.toLin'_apply, hP, Matrix.map_mul, ← Matrix.mulVec_mulVec, hv, h0, zero_smul,
      Matrix.mulVec_zero]
  · right
    have hσe : σ e = 1 := hinj (by rw [h1, map_one])
    have hle : RingHom.ker π ≤ RingHom.ker σ := by
      rw [hker, Ideal.span_le, Set.singleton_subset_iff]
      simp [RingHom.mem_ker, map_sub, hσe]
    refine ⟨π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ) ⟨σ, hle⟩,
      ?_⟩
    exact (RingHom.liftOfRightInverse_comp π _ _ ⟨σ, hle⟩).symm

end EigC

end GlobalTheory.DetInv.PartShift

namespace GlobalTheory.DetInv.PartShift

section Part

variable {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C]
  {Γ Λ : Type} [CommRing Γ] [CommRing Λ] {h h' : ℕ}
  {ρ : Γ → Matrix (Fin h) (Fin h) O} {ρ' : Λ → Matrix (Fin h') (Fin h') O}
  {π : Γ →+* Λ} {e : Γ} {P : Matrix (Fin h') (Fin h) O} {I : Matrix (Fin h) (Fin h') O}

/- English proof (translation)
Establish `: (1 - e) ∈ RingHom.ker π` using `hker ▸ Ideal.mem_span_singleton_self _`. Rewrite `this` using `[RingHom.mem_ker, map_sub, map_one, sub_eq_zero]`. Conclude with `this.symm`.
-/
theorem pi_e (hker : RingHom.ker π = Ideal.span {1 - e}) : π e = 1 := by
  have : (1 - e) ∈ RingHom.ker π := hker ▸ Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
  exact this.symm

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[Matrix.toLin'_apply]`. Conclude with `(RingHom.map_mulVec (algebraMap O C) X t i).symm`.
-/
theorem toLin_incl {m n : ℕ} (X : Matrix (Fin m) (Fin n) O) (t : Fin n → O) :
    Matrix.toLin' (X.map (algebraMap O C)) (incl C n t) = incl C m (X *ᵥ t) := by
  funext i
  rw [Matrix.toLin'_apply]
  exact (RingHom.map_mulVec (algebraMap O C) X t i).symm

/- English proof (translation)
Establish `: (⨆ σ : {σ : Γ →+* O // σ ≠ τ.comp π}, eig C ρ σ.1) ≤ (⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ' σ.1).comap (Matrix.toLin' (P.map (algebraMap O C)))`. Use `iSup_le ?_` and prove the remaining obligations. Introduce and unpack `⟨σ, hσ⟩ v hv`. Rewrite using `[Submodule.mem_comap]`. Break down `eq_zero_or_factors_of_mem_eigenspace C hPI hIP hact hπ hker hinj he2 σ hv with h0 | ⟨σ', rfl⟩` into its components or cases.

Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`. Establish `hne : σ' ≠ τ` using `fun hh => hσ (by rw [hh])`. Conclude with `Submodule.mem_iSup_of_mem (⟨σ', hne⟩ : {σ : Λ →+* O // σ ≠ τ}) (eig_P C hIP hact hπ (pi_e hker) σ' hv)`. Conclude with `this hs`.
-/
theorem sup_P (hPI : P * I = 1) (hIP : I * P = ρ e) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = Ideal.span {1 - e})
    (hinj : Function.Injective (algebraMap O C)) (he2 : IsIdempotentElem e) (τ : Λ →+* O)
    {s : Fin h → C} (hs : s ∈ ⨆ σ : {σ : Γ →+* O // σ ≠ τ.comp π}, eig C ρ σ.1) :
    Matrix.toLin' (P.map (algebraMap O C)) s ∈ ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ' σ.1 := by
  have : (⨆ σ : {σ : Γ →+* O // σ ≠ τ.comp π}, eig C ρ σ.1) ≤
      (⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ' σ.1).comap
        (Matrix.toLin' (P.map (algebraMap O C))) := by
    refine iSup_le ?_
    rintro ⟨σ, hσ⟩ v hv
    rw [Submodule.mem_comap]
    rcases eq_zero_or_factors_of_mem_eigenspace C hPI hIP hact hπ hker hinj he2 σ hv with h0 | ⟨σ', rfl⟩
    · rw [h0]; exact Submodule.zero_mem _
    · have hne : σ' ≠ τ := fun hh => hσ (by rw [hh])
      exact Submodule.mem_iSup_of_mem (⟨σ', hne⟩ : {σ : Λ →+* O // σ ≠ τ})
        (eig_P C hIP hact hπ (pi_e hker) σ' hv)
  exact this hs

/- English proof (translation)
Establish `: (⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ' σ.1) ≤ (⨆ σ : {σ : Γ →+* O // σ ≠ τ.comp π}, eig C ρ σ.1).comap (Matrix.toLin' (I.map (algebraMap O C)))`. Use `iSup_le ?_` and prove the remaining obligations. Introduce and unpack `⟨σ, hσ⟩ v hv`. Rewrite using `[Submodule.mem_comap]`. Establish `hne : σ.comp π ≠ τ.comp π`.

Introduce `hh`. Use `hσ (RingHom.ext fun a => ?_)` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hπ a`. Conclude with `RingHom.congr_fun hh x`. Conclude with `Submodule.mem_iSup_of_mem (⟨σ.comp π, hne⟩ : {σ : Γ →+* O // σ ≠ τ.comp π}) (eig_I C hPI hIP hcomm hact σ hv)`.

Conclude with `this hs`.
-/
theorem sup_I (hPI : P * I = 1) (hIP : I * P = ρ e)
    (hcomm : ∀ x, ρ x * ρ e = ρ e * ρ x) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (hπ : Function.Surjective π) (τ : Λ →+* O)
    {s : Fin h' → C} (hs : s ∈ ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ' σ.1) :
    Matrix.toLin' (I.map (algebraMap O C)) s ∈
      ⨆ σ : {σ : Γ →+* O // σ ≠ τ.comp π}, eig C ρ σ.1 := by
  have : (⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ' σ.1) ≤
      (⨆ σ : {σ : Γ →+* O // σ ≠ τ.comp π}, eig C ρ σ.1).comap
        (Matrix.toLin' (I.map (algebraMap O C))) := by
    refine iSup_le ?_
    rintro ⟨σ, hσ⟩ v hv
    rw [Submodule.mem_comap]
    have hne : σ.comp π ≠ τ.comp π := by
      intro hh
      refine hσ (RingHom.ext fun a => ?_)
      obtain ⟨x, rfl⟩ := hπ a
      exact RingHom.congr_fun hh x
    exact Submodule.mem_iSup_of_mem (⟨σ.comp π, hne⟩ : {σ : Γ →+* O // σ ≠ τ.comp π})
      (eig_I C hPI hIP hcomm hact σ hv)
  exact this hs

/- English proof (translation)
Take `⟨h1, h2⟩` from `hy`. Use `⟨eig_P C hIP hact hπ (pi_e hker) τ h1, ?_⟩` and prove the remaining obligations. Take `⟨a, ⟨t, ht, rfl⟩, b, hb, rfl⟩` from `Submodule.mem_sup.1 h2`. Rewrite using `[map_add, toLin_incl]`. Conclude with `Submodule.add_mem_sup ⟨_, hL t ht, rfl⟩ (sup_P C hPI hIP hact hπ hker hinj he2 τ hb)`.
-/
theorem eigPart_P (hPI : P * I = 1) (hIP : I * P = ρ e) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = Ideal.span {1 - e})
    (hinj : Function.Injective (algebraMap O C)) (he2 : IsIdempotentElem e) (τ : Λ →+* O)
    {L : Submodule O (Fin h → O)} {L' : Submodule O (Fin h' → O)} (hL : ∀ t ∈ L, P *ᵥ t ∈ L')
    {y : Fin h → C} (hy : y ∈ eigPart C ρ (τ.comp π) L) :
    Matrix.toLin' (P.map (algebraMap O C)) y ∈ eigPart C ρ' τ L' := by
  obtain ⟨h1, h2⟩ := hy
  refine ⟨eig_P C hIP hact hπ (pi_e hker) τ h1, ?_⟩
  obtain ⟨a, ⟨t, ht, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 h2
  rw [map_add, toLin_incl]
  exact Submodule.add_mem_sup ⟨_, hL t ht, rfl⟩ (sup_P C hPI hIP hact hπ hker hinj he2 τ hb)

/- English proof (translation)
Take `⟨h1, h2⟩` from `hy`. Use `⟨eig_I C hPI hIP hcomm hact τ h1, ?_⟩` and prove the remaining obligations. Take `⟨a, ⟨t, ht, rfl⟩, b, hb, rfl⟩` from `Submodule.mem_sup.1 h2`. Rewrite using `[map_add, toLin_incl]`. Conclude with `Submodule.add_mem_sup ⟨_, hL t ht, rfl⟩ (sup_I C hPI hIP hcomm hact hπ τ hb)`.
-/
theorem eigPart_I (hPI : P * I = 1) (hIP : I * P = ρ e)
    (hcomm : ∀ x, ρ x * ρ e = ρ e * ρ x) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (hπ : Function.Surjective π) (τ : Λ →+* O)
    {L : Submodule O (Fin h → O)} {L' : Submodule O (Fin h' → O)} (hL : ∀ t ∈ L', I *ᵥ t ∈ L)
    {y : Fin h' → C} (hy : y ∈ eigPart C ρ' τ L') :
    Matrix.toLin' (I.map (algebraMap O C)) y ∈ eigPart C ρ (τ.comp π) L := by
  obtain ⟨h1, h2⟩ := hy
  refine ⟨eig_I C hPI hIP hcomm hact τ h1, ?_⟩
  obtain ⟨a, ⟨t, ht, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 h2
  rw [map_add, toLin_incl]
  exact Submodule.add_mem_sup ⟨_, hL t ht, rfl⟩ (sup_I C hPI hIP hcomm hact hπ τ hb)

/- English proof (translation)
Take `⟨hli, hsp⟩` from `hx`. Establish `hmem : ∀ i, x i ∈ S` using `fun i => hsp ▸ Submodule.subset_span ⟨i, rfl⟩`. Prove the components needed by the constructor for the conclusion. Use `LinearIndependent.of_comp g ?_` and prove the remaining obligations. Establish `: (⇑g ∘ fun i => f (x i)) = x` using `funext fun i => (h1 _ (hmem i)).2`.

Rewrite using `[this]`. Conclude with `hli`. Establish `: (Set.range fun i => f (x i)) = (f.restrictScalars O) '' Set.range x`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression.

Rewrite using `[this, Submodule.span_image, hsp]`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `(h1 y hy).1`. Introduce `y hy`.

Take `⟨z, hz, rfl⟩` from `h2 y hy`. Conclude with `⟨z, hz, rfl⟩`.
-/
theorem basis_transport (f : (Fin h → C) →ₗ[C] (Fin h' → C)) (g : (Fin h' → C) →ₗ[C] (Fin h → C))
    {S : Submodule O (Fin h → C)} {S' : Submodule O (Fin h' → C)}
    (h1 : ∀ x ∈ S, f x ∈ S' ∧ g (f x) = x) (h2 : ∀ y ∈ S', ∃ x ∈ S, f x = y)
    {n : ℕ} {x : Fin n → Fin h → C} (hx : IsBasisOf C S x) :
    IsBasisOf C S' (fun i => f (x i)) := by
  obtain ⟨hli, hsp⟩ := hx
  have hmem : ∀ i, x i ∈ S := fun i => hsp ▸ Submodule.subset_span ⟨i, rfl⟩
  constructor
  · refine LinearIndependent.of_comp g ?_
    have : (⇑g ∘ fun i => f (x i)) = x := funext fun i => (h1 _ (hmem i)).2
    rw [this]; exact hli
  · have : (Set.range fun i => f (x i)) = (f.restrictScalars O) '' Set.range x := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, hsp]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact (h1 y hy).1
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := h2 y hy
      exact ⟨z, hz, rfl⟩

/- English proof (translation)
Use `LinearEquiv.finrank_eq (LinearEquiv.ofLinear (g.restrict fun y hy => (h2 y hy).1) (f.restrict fun x hx => (h1 x hx).1) ?_ ?_)` and prove the remaining obligations. Use extensionality with `x : 2`. Conclude with `(h1 x.1 x.2).2`. Use extensionality with `y : 2`. Conclude with `(h2 y.1 y.2).2`.
-/
theorem finrank_eq_of_inverse {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    {S : Submodule R M} {S' : Submodule R N}
    (h1 : ∀ x ∈ S, f x ∈ S' ∧ g (f x) = x) (h2 : ∀ y ∈ S', g y ∈ S ∧ f (g y) = y) :
    Module.finrank R S' = Module.finrank R S := by
  refine LinearEquiv.finrank_eq (LinearEquiv.ofLinear (g.restrict fun y hy => (h2 y hy).1)
    (f.restrict fun x hx => (h1 x hx).1) ?_ ?_)
  · ext x : 2
    exact (h1 x.1 x.2).2
  · ext y : 2
    exact (h2 y.1 y.2).2

end Part

end GlobalTheory.DetInv.PartShift

namespace GlobalTheory.DetInv.PartShift

section Data

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C]
  {ε : PreTilt O p} {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

/- English proof (translation)
Simplify using `[Datum.Tsub, actT, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]`.
-/
theorem mem_Tsub_iff (D : Datum ε h Λ) (σ : Λ →+* O) (t : Fin h → O) :
    t ∈ D.Tsub σ ↔ ∀ a, (actT D a).map (algebraMap O O) *ᵥ t = algebraMap O O (σ a) • t := by
  simp [Datum.Tsub, actT, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem map_ofPadic_theta {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℤ_[p]) :
    (X.map (ofPadic p O)).map (WittVector.fontaineTheta O p) = X.map (padicToO p O) := rfl

end Data

end GlobalTheory.DetInv.PartShift

namespace GlobalTheory.DetInv

open PartShift

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv ε hε Γ _ _ Λ _ _ π e he2 hπ hker h h' D D' iT pT iM pM ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ _ _ τ`. Establish `hinj : Function.Injective (algebraMap O C)` using `hv.hom_inj`. Take `⟨-, -, hG, -, -⟩` from `datum_scalar_intertwine p C v O hv ε hε Γ h D`. Take `⟨π₀, hπ₀⟩ : ∃ π₀ : Γ →+* Λ, π₀ = (π : Γ →+* Λ)` from `⟨_, rfl⟩`. Establish `hππ : ∀ x, π x = π₀ x` using `fun x => by rw [hπ₀]; rfl`.

Establish `hπ' : Function.Surjective π₀` using `by rw [hπ₀]; exact hπ`. Establish `hker' : RingHom.ker π₀ = Ideal.span {1 - e}` using `by rw [hπ₀]; exact hker`. Rewrite using `[← hπ₀]`. Establish `he : π₀ e = 1` using `pi_e hker'`. Take `⟨P, hP⟩ : ∃ P, P = pT.map (padicToO p O)` from `⟨_, rfl⟩`.

Take `⟨I, hI⟩ : ∃ I, I = iT.map (padicToO p O)` from `⟨_, rfl⟩`. Take `⟨Q, hQ⟩ : ∃ Q, Q = pM.map (WittVector.fontaineTheta O p)` from `⟨_, rfl⟩`. Take `⟨J, hJ⟩ : ∃ J, J = iM.map (WittVector.fontaineTheta O p)` from `⟨_, rfl⟩`. Take `⟨F, hF⟩ : ∃ F, F = D.F.map (WittVector.fontaineTheta O p)` from `⟨_, rfl⟩`. Take `⟨G, hG0⟩ : ∃ G, G = D.G.map (WittVector.fontaineTheta O p)` from `⟨_, rfl⟩`.

Establish `hPI : P * I = 1`. Rewrite using `[hP, hI, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hIP : I * P = actT D e` using `by rw [hP, hI, ← Matrix.map_mul, h2]; rfl`. Establish `hQJ : Q * J = 1`. Rewrite using `[hQ, hJ, ← Matrix.map_mul, h3, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `hJQ : J * Q = actH D e` using `by rw [hQ, hJ, ← Matrix.map_mul, h4]; rfl`. Establish `hcT : ∀ x, actT D x * actT D e = actT D e * actT D x` using `fun x => by`. Simplify using `only [actT, ← Matrix.map_mul, ← map_mul, mul_comm x e]`. Establish `hcH : ∀ x, actH D x * actH D e = actH D e * actH D x` using `fun x => by`. Simplify using `only [actH, ← Matrix.map_mul, ← map_mul, mul_comm x e]`.

Establish `haT : ∀ x, actT D' (π₀ x) = P * actT D x * I` using `fun x => by`. Rewrite using `[← hππ, actT, h7, Matrix.map_mul, Matrix.map_mul, hP, hI]`. Both sides reduce to the same expression. Establish `haH : ∀ x, actH D' (π₀ x) = Q * actH D x * J` using `fun x => by`. Rewrite using `[← hππ, actH, h8, Matrix.map_mul, Matrix.map_mul, hQ, hJ]`.

Both sides reduce to the same expression. Establish `hF' : D'.F.map (WittVector.fontaineTheta O p) = Q * F * I`. Rewrite using `[h5, Matrix.map_mul, Matrix.map_mul, map_ofPadic_theta, hQ, hF, hI]`. Establish `hG' : D'.G.map (WittVector.fontaineTheta O p) = P * G * J`. Rewrite using `[h6, Matrix.map_mul, Matrix.map_mul, map_ofPadic_theta, hP, hG0, hJ]`.

Establish `hFe : F * (I * P) = J * Q * F`. Rewrite using `[hIP, hJQ, hF, actT, actH, ← map_ofPadic_theta, ← Matrix.map_mul, D.F_act, Matrix.map_mul]`. Establish `hGe : G * (J * Q) = I * P * G`. Rewrite using `[hIP, hJQ, hG0, actT, actH, ← map_ofPadic_theta, ← Matrix.map_mul, hG, Matrix.map_mul]`. Establish `g1 : P * G * J * Q = P * G`.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, hGe, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPI, Matrix.one_mul]`. Establish `g2 : I * (P * G * J) = G * J`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hGe, Matrix.mul_assoc, Matrix.mul_assoc, hQJ, Matrix.mul_one]`. Establish `f1 : Q * F * I * P = Q * F`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, hFe, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQJ, Matrix.one_mul]`.

Establish `f2 : J * (Q * F * I) = F * I`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hFe, Matrix.mul_assoc, Matrix.mul_assoc, hPI, Matrix.mul_one]`. Establish `hbb : ∀ t, D.bb t = G *ᵥ t` using `fun t => by rw [hG0]; rfl`. Establish `hbb' : ∀ t, D'.bb t = (P * G * J) *ᵥ t` using `fun t => by rw [← hG']; rfl`. Establish `hal : ∀ w, alC C D w = F.map (algebraMap O C) *ᵥ w` using `fun t => by rw [hF]; rfl`.

Establish `hal' : ∀ w, alC C D' w = (Q * F * I).map (algebraMap O C) *ᵥ w` using `fun t => by`. Rewrite using `[← hF']`. Both sides reduce to the same expression. Establish `lie1 : ∀ u ∈ D.Lie ⊓ D.Tsub (τ.comp π₀), P *ᵥ u ∈ D'.Lie ⊓ D'.Tsub τ ∧ I *ᵥ (P *ᵥ u) = u`. Introduce and unpack `u ⟨⟨y, hy⟩, hu⟩`.

Establish `hu'` using `(mem_Tsub_iff D _ u).1 hu`. Use `⟨⟨⟨Q *ᵥ y, ?_⟩, (mem_Tsub_iff D' _ _).2 fun a => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, hbb, hbb', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, g1]`. Simplify using `using mulVec_mem_eigenspace hIP haT hπ' he τ u hu' a`. Simplify using `using mulVec_mulVec_eq_self_of_eigenvector hIP he τ u hu'`.

Establish `lie2 : ∀ u ∈ D'.Lie ⊓ D'.Tsub τ, I *ᵥ u ∈ D.Lie ⊓ D.Tsub (τ.comp π₀) ∧ P *ᵥ (I *ᵥ u) = u`. Introduce and unpack `u ⟨⟨y, hy⟩, hu⟩`. Establish `hu'` using `(mem_Tsub_iff D' _ u).1 hu`. Use `⟨⟨⟨J *ᵥ y, ?_⟩, (mem_Tsub_iff D _ _).2 fun a => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, hbb, hbb', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, g2]`.

Simplify using `using I_eigen hPI hIP hcT haT τ u hu' a`. Rewrite using `[Matrix.mulVec_mulVec, hPI, Matrix.one_mulVec]`. Use `⟨finrank_eq_of_inverse (Matrix.toLin' P) (Matrix.toLin' I) lie1 lie2, finrank_eq_of_inverse (Matrix.toLin' (P.map (algebraMap O C))) (Matrix.toLin' (I.map (algebraMap O C))) (fun x hx => ⟨eig_P C hIP haT hπ' he τ hx, eig_IP C hIP he τ hx⟩) (fun y hy => ⟨eig_I C hPI hIP hcT haT τ …` and prove the remaining obligations. Introduce `r hr a b x g m k hx hg hm hk`. Establish `tP : ∀ y ∈ eigPart C (actT D) (τ.comp π₀) ⊤, Matrix.toLin' (P.map (algebraMap O C)) y ∈ eigPart C (actT D') τ ⊤` using `fun y hy => eigPart_P C hPI hIP haT hπ' hker' hinj he2 τ (fun _ _ => Submodule.mem_top) hy`.

Establish `tI : ∀ y ∈ eigPart C (actT D') τ ⊤, Matrix.toLin' (I.map (algebraMap O C)) y ∈ eigPart C (actT D) (τ.comp π₀) ⊤` using `fun y hy => eigPart_I C hPI hIP hcT haT hπ' τ (fun _ _ => Submodule.mem_top) hy`. Establish `a1 : ∀ w, alC C D' (Matrix.toLin' (P.map (algebraMap O C)) w) = Matrix.toLin' (Q.map (algebraMap O C)) (alC C D w)` using `fun w => by`. Rewrite using `[hal, hal', Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, f1]`. Establish `a2 : ∀ w, alC C D (Matrix.toLin' (I.map (algebraMap O C)) w) = Matrix.toLin' (J.map (algebraMap O C)) (alC C D' w)` using `fun w => by`. Rewrite using `[hal, hal', Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, f2]`.

Use `hr a b (fun i => Matrix.toLin' (P.map (algebraMap O C)) (x i)) g (fun i => Matrix.toLin' (Q.map (algebraMap O C)) (m i)) k ?_ ?_ ?_ ?_` and prove the remaining obligations. Use `basis_transport C _ (Matrix.toLin' (I.map (algebraMap O C))) ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Rewrite using `[toLin_incl, toLin_incl, (lie1 u hu).2]`. Conclude with `⟨⟨_, (lie1 u hu).1, rfl⟩, rfl⟩`.

Introduce and unpack `_ ⟨u, hu, rfl⟩`. Conclude with `⟨_, ⟨_, (lie2 u hu).1, rfl⟩, by rw [toLin_incl, (lie2 u hu).2]⟩`. Use `basis_transport C (Matrix.toLin' (P.map (algebraMap O C))) (Matrix.toLin' (I.map (algebraMap O C))) (S' := wQuot C D' τ) ?_ ?_ hg` as an intermediate fact. Simplify `this` using `only [map_sum, map_smul]`. Introduce and unpack `y ⟨hy, hy0⟩`.

Use `⟨⟨tP y hy, ?_⟩, eig_IP C hIP he τ hy.1⟩` and prove the remaining obligations. Establish `hy1 : alC C D y = 0` using `hy0`. Use `show alC C D' _ = 0`. Rewrite using `[a1, hy1, map_zero]`. Introduce and unpack `y ⟨hy, hy0⟩`.

Use `⟨_, ⟨tI y hy, ?_⟩, eig_PI C hPI y⟩` and prove the remaining obligations. Establish `hy1 : alC C D' y = 0` using `hy0`. Use `show alC C D _ = 0`. Rewrite using `[a2, hy1, map_zero]`. Use `basis_transport C _ (Matrix.toLin' (J.map (algebraMap O C))) ?_ ?_ hm` and prove the remaining obligations.

Introduce `y hy`. Use `⟨eigPart_P C hQJ hJQ haH hπ' hker' hinj he2 τ (fun t ht => ?_) hy, eig_IP C hJQ he τ hy.1⟩` and prove the remaining obligations. Establish `ht1 : D.bb t = 0` using `ht`. Use `show D'.bb _ = 0`. Rewrite `ht1` using `[hbb]`.

Rewrite using `[hbb', Matrix.mulVec_mulVec, g1, ← Matrix.mulVec_mulVec, ht1, Matrix.mulVec_zero]`. Introduce `y hy`. Use `⟨_, eigPart_I C hQJ hJQ hcH haH hπ' τ (fun t ht => ?_) hy, eig_PI C hQJ y⟩` and prove the remaining obligations. Establish `ht1 : D'.bb t = 0` using `ht`. Use `show D.bb _ = 0`.

Rewrite `ht1` using `[hbb']`. Rewrite using `[hbb, Matrix.mulVec_mulVec, ← g2, ← Matrix.mulVec_mulVec, ht1, Matrix.mulVec_zero]`. Use `basis_transport C (Matrix.toLin' (Q.map (algebraMap O C))) (Matrix.toLin' (J.map (algebraMap O C))) (S' := alQuot C D' τ) ?_ ?_ hk` as an intermediate fact. Simplify `this` using `only [map_sum, map_smul]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Use `⟨⟨_, tP w hw, a1 w⟩, ?_⟩` and prove the remaining obligations. Use `show Matrix.toLin' _ (Matrix.toLin' _ (alC C D w)) = alC C D w`. Rewrite using `[← a1, ← a2, eig_IP C hIP he τ hw.1]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Use `⟨_, ⟨_, tI w hw, rfl⟩, ?_⟩` and prove the remaining obligations.

Use `show Matrix.toLin' _ (alC C D _) = alC C D' w`. Rewrite using `[← a1, eig_PI C hPI]`.
-/
theorem part_rank_dim_shift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Γ : Type) [CommRing Γ] [Algebra ℤ_[p] Γ] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (π : Γ →ₐ[ℤ_[p]] Λ) (e : Γ), IsIdempotentElem e → Function.Surjective π → RingHom.ker π = Ideal.span {1 - e} → ∀ (h h' : ℕ) (D : Datum ε h Γ) (D' : Datum ε h' Λ) (iT : Matrix (Fin h) (Fin h') ℤ_[p]) (pT : Matrix (Fin h') (Fin h) ℤ_[p]) (iM : Matrix (Fin h) (Fin h') (Ainf p O)) (pM : Matrix (Fin h') (Fin h) (Ainf p O)), (pT * iT = 1 ∧ iT * pT = D.ρT e ∧ pM * iM = 1 ∧ iM * pM = D.ρM e ∧ D'.F = pM * D.F * iT.map (ofPadic p O) ∧ D'.G = pT.map (ofPadic p O) * D.G * iM ∧ (∀ x, D'.ρT (π x) = pT * D.ρT x * iT) ∧ ∀ x, D'.ρM (π x) = pM * D.ρM x * iM) → (⨆ σ : Γ →+* O, eig C (actT D) σ) = ⊤ → (⨆ σ : Γ →+* O, eig C (actH D) σ) = ⊤ → ∀ τ : Λ →+* O, D'.lieRank τ = D.lieRank (τ.comp (π : Γ →+* Λ)) ∧ Module.finrank C (eig C (actT D') τ) = Module.finrank C (eig C (actT D) (τ.comp (π : Γ →+* Λ))) ∧ ∀ r, IsShift C v D' τ r → IsShift C v D (τ.comp (π : Γ →+* Λ)) r := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Γ _ _ Λ _ _ π e he2 hπ hker h h' D D' iT pT iM pM
    ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ _ _ τ
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  obtain ⟨-, -, hG, -, -⟩ := datum_scalar_intertwine p C v O hv ε hε Γ h D
  obtain ⟨π₀, hπ₀⟩ : ∃ π₀ : Γ →+* Λ, π₀ = (π : Γ →+* Λ) := ⟨_, rfl⟩
  have hππ : ∀ x, π x = π₀ x := fun x => by rw [hπ₀]; rfl
  have hπ' : Function.Surjective π₀ := by rw [hπ₀]; exact hπ
  have hker' : RingHom.ker π₀ = Ideal.span {1 - e} := by rw [hπ₀]; exact hker
  rw [← hπ₀]
  have he : π₀ e = 1 := pi_e hker'
  obtain ⟨P, hP⟩ : ∃ P, P = pT.map (padicToO p O) := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I, I = iT.map (padicToO p O) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = pM.map (WittVector.fontaineTheta O p) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = iM.map (WittVector.fontaineTheta O p) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = D.F.map (WittVector.fontaineTheta O p) := ⟨_, rfl⟩
  obtain ⟨G, hG0⟩ : ∃ G, G = D.G.map (WittVector.fontaineTheta O p) := ⟨_, rfl⟩
  have hPI : P * I = 1 := by
    rw [hP, hI, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hIP : I * P = actT D e := by rw [hP, hI, ← Matrix.map_mul, h2]; rfl
  have hQJ : Q * J = 1 := by
    rw [hQ, hJ, ← Matrix.map_mul, h3, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJQ : J * Q = actH D e := by rw [hQ, hJ, ← Matrix.map_mul, h4]; rfl
  have hcT : ∀ x, actT D x * actT D e = actT D e * actT D x := fun x => by
    simp only [actT, ← Matrix.map_mul, ← map_mul, mul_comm x e]
  have hcH : ∀ x, actH D x * actH D e = actH D e * actH D x := fun x => by
    simp only [actH, ← Matrix.map_mul, ← map_mul, mul_comm x e]
  have haT : ∀ x, actT D' (π₀ x) = P * actT D x * I := fun x => by
    rw [← hππ, actT, h7, Matrix.map_mul, Matrix.map_mul, hP, hI]; rfl
  have haH : ∀ x, actH D' (π₀ x) = Q * actH D x * J := fun x => by
    rw [← hππ, actH, h8, Matrix.map_mul, Matrix.map_mul, hQ, hJ]; rfl
  have hF' : D'.F.map (WittVector.fontaineTheta O p) = Q * F * I := by
    rw [h5, Matrix.map_mul, Matrix.map_mul, map_ofPadic_theta, hQ, hF, hI]
  have hG' : D'.G.map (WittVector.fontaineTheta O p) = P * G * J := by
    rw [h6, Matrix.map_mul, Matrix.map_mul, map_ofPadic_theta, hP, hG0, hJ]
  have hFe : F * (I * P) = J * Q * F := by
    rw [hIP, hJQ, hF, actT, actH, ← map_ofPadic_theta, ← Matrix.map_mul, D.F_act, Matrix.map_mul]
  have hGe : G * (J * Q) = I * P * G := by
    rw [hIP, hJQ, hG0, actT, actH, ← map_ofPadic_theta, ← Matrix.map_mul, hG, Matrix.map_mul]
  have g1 : P * G * J * Q = P * G := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hGe, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPI,
      Matrix.one_mul]
  have g2 : I * (P * G * J) = G * J := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hGe, Matrix.mul_assoc, Matrix.mul_assoc, hQJ,
      Matrix.mul_one]
  have f1 : Q * F * I * P = Q * F := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hFe, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQJ,
      Matrix.one_mul]
  have f2 : J * (Q * F * I) = F * I := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hFe, Matrix.mul_assoc, Matrix.mul_assoc, hPI,
      Matrix.mul_one]
  have hbb : ∀ t, D.bb t = G *ᵥ t := fun t => by rw [hG0]; rfl
  have hbb' : ∀ t, D'.bb t = (P * G * J) *ᵥ t := fun t => by rw [← hG']; rfl
  have hal : ∀ w, alC C D w = F.map (algebraMap O C) *ᵥ w := fun t => by rw [hF]; rfl
  have hal' : ∀ w, alC C D' w = (Q * F * I).map (algebraMap O C) *ᵥ w := fun t => by
    rw [← hF']; rfl

  have lie1 : ∀ u ∈ D.Lie ⊓ D.Tsub (τ.comp π₀),
      P *ᵥ u ∈ D'.Lie ⊓ D'.Tsub τ ∧ I *ᵥ (P *ᵥ u) = u := by
    rintro u ⟨⟨y, hy⟩, hu⟩
    have hu' := (mem_Tsub_iff D _ u).1 hu
    refine ⟨⟨⟨Q *ᵥ y, ?_⟩, (mem_Tsub_iff D' _ _).2 fun a => ?_⟩, ?_⟩
    · rw [← hy, hbb, hbb', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, g1]
    · simpa using mulVec_mem_eigenspace hIP haT hπ' he τ u hu' a
    · simpa using mulVec_mulVec_eq_self_of_eigenvector hIP he τ u hu'
  have lie2 : ∀ u ∈ D'.Lie ⊓ D'.Tsub τ,
      I *ᵥ u ∈ D.Lie ⊓ D.Tsub (τ.comp π₀) ∧ P *ᵥ (I *ᵥ u) = u := by
    rintro u ⟨⟨y, hy⟩, hu⟩
    have hu' := (mem_Tsub_iff D' _ u).1 hu
    refine ⟨⟨⟨J *ᵥ y, ?_⟩, (mem_Tsub_iff D _ _).2 fun a => ?_⟩, ?_⟩
    · rw [← hy, hbb, hbb', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, g2]
    · simpa using I_eigen hPI hIP hcT haT τ u hu' a
    · rw [Matrix.mulVec_mulVec, hPI, Matrix.one_mulVec]
  refine ⟨finrank_eq_of_inverse (Matrix.toLin' P) (Matrix.toLin' I) lie1 lie2,
    finrank_eq_of_inverse (Matrix.toLin' (P.map (algebraMap O C)))
      (Matrix.toLin' (I.map (algebraMap O C)))
      (fun x hx => ⟨eig_P C hIP haT hπ' he τ hx, eig_IP C hIP he τ hx⟩)
      (fun y hy => ⟨eig_I C hPI hIP hcT haT τ hy, eig_PI C hPI y⟩), ?_⟩
  intro r hr a b x g m k hx hg hm hk
  have tP : ∀ y ∈ eigPart C (actT D) (τ.comp π₀) ⊤,
      Matrix.toLin' (P.map (algebraMap O C)) y ∈ eigPart C (actT D') τ ⊤ := fun y hy =>
    eigPart_P C hPI hIP haT hπ' hker' hinj he2 τ (fun _ _ => Submodule.mem_top) hy
  have tI : ∀ y ∈ eigPart C (actT D') τ ⊤,
      Matrix.toLin' (I.map (algebraMap O C)) y ∈ eigPart C (actT D) (τ.comp π₀) ⊤ := fun y hy =>
    eigPart_I C hPI hIP hcT haT hπ' τ (fun _ _ => Submodule.mem_top) hy
  have a1 : ∀ w, alC C D' (Matrix.toLin' (P.map (algebraMap O C)) w) =
      Matrix.toLin' (Q.map (algebraMap O C)) (alC C D w) := fun w => by
    rw [hal, hal', Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, f1]
  have a2 : ∀ w, alC C D (Matrix.toLin' (I.map (algebraMap O C)) w) =
      Matrix.toLin' (J.map (algebraMap O C)) (alC C D' w) := fun w => by
    rw [hal, hal', Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, f2]
  refine hr a b (fun i => Matrix.toLin' (P.map (algebraMap O C)) (x i)) g
    (fun i => Matrix.toLin' (Q.map (algebraMap O C)) (m i)) k ?_ ?_ ?_ ?_
  · refine basis_transport C _ (Matrix.toLin' (I.map (algebraMap O C))) ?_ ?_ hx
    · rintro _ ⟨u, hu, rfl⟩
      rw [toLin_incl, toLin_incl, (lie1 u hu).2]
      exact ⟨⟨_, (lie1 u hu).1, rfl⟩, rfl⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact ⟨_, ⟨_, (lie2 u hu).1, rfl⟩, by rw [toLin_incl, (lie2 u hu).2]⟩
  · have := basis_transport C (Matrix.toLin' (P.map (algebraMap O C)))
      (Matrix.toLin' (I.map (algebraMap O C))) (S' := wQuot C D' τ) ?_ ?_ hg
    · simpa only [map_sum, map_smul] using this
    · rintro y ⟨hy, hy0⟩
      refine ⟨⟨tP y hy, ?_⟩, eig_IP C hIP he τ hy.1⟩
      have hy1 : alC C D y = 0 := hy0
      show alC C D' _ = 0
      rw [a1, hy1, map_zero]
    · rintro y ⟨hy, hy0⟩
      refine ⟨_, ⟨tI y hy, ?_⟩, eig_PI C hPI y⟩
      have hy1 : alC C D' y = 0 := hy0
      show alC C D _ = 0
      rw [a2, hy1, map_zero]
  · refine basis_transport C _ (Matrix.toLin' (J.map (algebraMap O C))) ?_ ?_ hm
    · intro y hy
      refine ⟨eigPart_P C hQJ hJQ haH hπ' hker' hinj he2 τ (fun t ht => ?_) hy,
        eig_IP C hJQ he τ hy.1⟩
      have ht1 : D.bb t = 0 := ht
      show D'.bb _ = 0
      rw [hbb] at ht1
      rw [hbb', Matrix.mulVec_mulVec, g1, ← Matrix.mulVec_mulVec, ht1, Matrix.mulVec_zero]
    · intro y hy
      refine ⟨_, eigPart_I C hQJ hJQ hcH haH hπ' τ (fun t ht => ?_) hy, eig_PI C hQJ y⟩
      have ht1 : D'.bb t = 0 := ht
      show D.bb _ = 0
      rw [hbb'] at ht1
      rw [hbb, Matrix.mulVec_mulVec, ← g2, ← Matrix.mulVec_mulVec, ht1, Matrix.mulVec_zero]
  · have := basis_transport C (Matrix.toLin' (Q.map (algebraMap O C)))
      (Matrix.toLin' (J.map (algebraMap O C))) (S' := alQuot C D' τ) ?_ ?_ hk
    · simpa only [map_sum, map_smul] using this
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨⟨_, tP w hw, a1 w⟩, ?_⟩
      show Matrix.toLin' _ (Matrix.toLin' _ (alC C D w)) = alC C D w
      rw [← a1, ← a2, eig_IP C hIP he τ hw.1]
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨_, ⟨_, tI w hw, rfl⟩, ?_⟩
      show Matrix.toLin' _ (alC C D _) = alC C D' w
      rw [← a1, eig_PI C hPI]

end GlobalTheory.DetInv
