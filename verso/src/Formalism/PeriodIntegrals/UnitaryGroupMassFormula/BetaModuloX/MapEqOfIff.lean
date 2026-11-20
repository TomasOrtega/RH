import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.HQTracePos

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaModX

section Q3

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [Submodule.mem_map, LinearEquiv.coe_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `(h w).2 hw`.

Introduce `hv`. Use `⟨γ.symm v, (h _).1 ?_, by simp⟩` and prove the remaining obligations. Simplify using `using hv`.
-/
theorem map_eq_of_iff (γ : S.V ≃ₗ[E] S.V) {U : Submodule E S.V} (h : ∀ v, γ v ∈ U ↔ v ∈ U) :
    U.map (γ : S.V →ₗ[E] S.V) = U := by
  ext v
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (h w).2 hw
  · intro hv
    refine ⟨γ.symm v, (h _).1 ?_, by simp⟩
    simpa using hv

/- English proof (translation)
Simplify using `only [Uo, mem_orth']`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Establish `h1` using `h (γ x) ((hX x).2 hx)`. Rewrite `h1` using `[hiso]`. Then use the resulting hypothesis.

Introduce `h x hx`. Establish `hx' : γ.symm x ∈ Xsp F'` using `(hX _).1 (by simpa using hx)`. Establish `h1` using `h _ hx'`. Rewrite `h1` using `[← hiso, LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis.
-/
theorem orth_iff {T' : E} (F' : LFlag S r T') (γ : S.V ≃ₗ[E] S.V) (hiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y)
    (hX : ∀ v, γ v ∈ Xsp F' ↔ v ∈ Xsp F') (v : S.V) : γ v ∈ Uo F' ↔ v ∈ Uo F' := by
  simp only [Uo, mem_orth']
  constructor
  · intro h x hx
    have h1 := h (γ x) ((hX x).2 hx)
    rwa [hiso] at h1
  · intro h x hx
    have hx' : γ.symm x ∈ Xsp F' := (hX _).1 (by simpa using hx)
    have h1 := h _ hx'
    rwa [← hiso, LinearEquiv.apply_symm_apply] at h1

def γU {T' : E} (F' : LFlag S r T') (γ : S.V ≃ₗ[E] S.V) (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F') :
    Uo F' ≃ₗ[E] Uo F' :=
  γ.ofSubmodules _ _ (map_eq_of_iff γ hU)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem γU_coe {T' : E} (F' : LFlag S r T') (γ : S.V ≃ₗ[E] S.V) (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F')
    (a : Uo F') : (γU F' γ hU a : S.V) = γ a := rfl

/- English proof (translation)
Use `first`. Consider the case `exact LinearEquiv.ofSubmodules_symm_apply _`. Consider the case `simp [γU]`.
-/
theorem γU_symm_coe {T' : E} (F' : LFlag S r T') (γ : S.V ≃ₗ[E] S.V) (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F')
    (a : Uo F') : (((γU F' γ hU).symm a : Uo F') : S.V) = γ.symm a := by
  first
    | exact LinearEquiv.ofSubmodules_symm_apply _
    | simp [γU]

def γQ {T' : E} (F' : LFlag S r T') (γ : S.V ≃ₗ[E] S.V) (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F')
    (hX : ∀ v, γ v ∈ Xsp F' ↔ v ∈ Xsp F') : Qt F' ≃ₗ[E] Qt F' :=
  Submodule.Quotient.equiv (Pk F') (Pk F') (γU F' γ hU) (by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      show γ (b : S.V) ∈ Xsp F'
      exact (hX _).2 hb
    · intro ha
      refine ⟨(γU F' γ hU).symm a, ?_, by simp⟩
      show (((γU F' γ hU).symm a : Uo F') : S.V) ∈ Xsp F'
      rw [γU_symm_coe]
      apply (hX _).1
      rw [LinearEquiv.apply_symm_apply]
      exact ha)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem γQ_mk {T' : E} (F' : LFlag S r T') (γ : S.V ≃ₗ[E] S.V) (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F')
    (hX : ∀ v, γ v ∈ Xsp F' ↔ v ∈ Xsp F') (a : Uo F') :
    γQ F' γ hU hX (Submodule.Quotient.mk a) = Submodule.Quotient.mk (γU F' γ hU a) := rfl

/- English proof (translation)
Use `show ∀ x y, (hQ F' c) ((γQ F' γ hU hX) x) ((γQ F' γ hU hX) y) = (hQ F' c) x y`. Introduce `x y`. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H a`. Proceed by induction on `y using Submodule.Quotient.induction_on with`.

Consider the case `H b`. Rewrite using `[γQ_mk, γQ_mk, hQ_mk, hQ_mk, hV_apply, hV_apply, γU_coe, γU_coe]`. Use `conv_lhs => rw [← hz]`. Simplify using `only [hiso]`.
-/
theorem γQ_isom {T' : E} (F' : LFlag S r T') (γ : S.V ≃ₗ[E] S.V) (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F')
    (hX : ∀ v, γ v ∈ Xsp F' ↔ v ∈ Xsp F') (hiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y)
    (hz : γ F'.fl.z = F'.fl.z) (c : E) : γQ F' γ hU hX ∈ Formalism.HermitianLatticesTheory.isom (hQ F' c) := by
  show ∀ x y, (hQ F' c) ((γQ F' γ hU hX) x) ((γQ F' γ hU hX) y) = (hQ F' c) x y
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H a =>
  induction y using Submodule.Quotient.induction_on with
  | H b =>
  rw [γQ_mk, γQ_mk, hQ_mk, hQ_mk, hV_apply, hV_apply, γU_coe, γU_coe]
  conv_lhs => rw [← hz]
  simp only [hiso]

def ΛU {T' : E} (F' : LFlag S r T') (Λ : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) (Uo F') :=
  Λ.comap ((Uo F').subtype.restrictScalars (𝓞 E))

def Lb {T' : E} (F' : LFlag S r T') (Λ : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) (Qt F') :=
  (ΛU F' Λ).map ((Pk F').mkQ.restrictScalars (𝓞 E))

/- English proof (translation)
Use `first`. Consider the case `exact Iff.rfl`. Consider the case `(simp [Lb, ΛU]; done)`. Consider the case `(constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, rfl⟩)`.
-/
theorem mem_Lb {T' : E} (F' : LFlag S r T') (Λ : Submodule (𝓞 E) S.V) {q : Qt F'} :
    q ∈ Lb F' Λ ↔ ∃ a : Uo F', (a : S.V) ∈ Λ ∧ Submodule.Quotient.mk a = q := by
  first
    | exact Iff.rfl
    | (simp [Lb, ΛU]; done)
    | (constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, rfl⟩)

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hfg : Λ.FG` using `hΛ.fg`. Establish `hN : IsNoetherian (𝓞 E) Λ` using `isNoetherian_of_fg_of_noetherian Λ hfg`. Establish `h1 : (ΛU F' Λ).FG`. Apply `Submodule.fg_of_fg_map_injective ((Uo F').subtype.restrictScalars (𝓞 E)) Subtype.val_injective` to reduce the goal to its premises.

Establish `hle : (ΛU F' Λ).map ((Uo F').subtype.restrictScalars (𝓞 E)) ≤ Λ`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `ha`. Conclude with `(isNoetherian_submodule.1 hN) _ hle`. Conclude with `h1.map _`.

Rewrite using `[eq_top_iff]`. Introduce `q _`. Proceed by induction on `q using Submodule.Quotient.induction_on with`. Consider the case `H a`. Take `⟨o, ho, hoa⟩` from `PI.UnitaryGroupMassFormula.BetaLUniq.exists_smul_mem S Λ hΛ (a : S.V)`.

Establish `hmem : (Submodule.Quotient.mk (p` using `Pk F') (o • a) : Qt F') ∈ Lb F' Λ := (mem_Lb F' Λ).2 ⟨o • a, by simpa using hoa, rfl⟩`. Establish `ho' : (algebraMap (𝓞 E) E o) ≠ 0`. Rewrite using `[ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]` and apply the resulting hypothesis. Establish `: (Submodule.Quotient.mk (p` using `Pk F') a : Qt F') = (algebraMap (𝓞 E) E o)⁻¹ • (Submodule.Quotient.mk (p := Pk F') (o • a) : Qt F') := by`. Rewrite using `[Submodule.Quotient.mk_smul, ← algebraMap_smul E o, smul_smul, inv_mul_cancel₀ ho', one_smul]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem Lb_lattice {T' : E} (F' : LFlag S r T') (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) :
    Submodule.IsLattice E (Lb F' Λ) := by
  refine ⟨?_, ?_⟩
  · have hfg : Λ.FG := hΛ.fg
    have hN : IsNoetherian (𝓞 E) Λ := isNoetherian_of_fg_of_noetherian Λ hfg
    have h1 : (ΛU F' Λ).FG := by
      apply Submodule.fg_of_fg_map_injective ((Uo F').subtype.restrictScalars (𝓞 E)) Subtype.val_injective
      have hle : (ΛU F' Λ).map ((Uo F').subtype.restrictScalars (𝓞 E)) ≤ Λ := by
        rintro _ ⟨a, ha, rfl⟩
        exact ha
      exact (isNoetherian_submodule.1 hN) _ hle
    exact h1.map _
  · rw [eq_top_iff]
    intro q _
    induction q using Submodule.Quotient.induction_on with
    | H a =>
      obtain ⟨o, ho, hoa⟩ := PI.UnitaryGroupMassFormula.BetaLUniq.exists_smul_mem S Λ hΛ (a : S.V)
      have hmem : (Submodule.Quotient.mk (p := Pk F') (o • a) : Qt F') ∈ Lb F' Λ :=
        (mem_Lb F' Λ).2 ⟨o • a, by simpa using hoa, rfl⟩
      have ho' : (algebraMap (𝓞 E) E o) ≠ 0 := by
        rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]
      have : (Submodule.Quotient.mk (p := Pk F') a : Qt F') =
          (algebraMap (𝓞 E) E o)⁻¹ • (Submodule.Quotient.mk (p := Pk F') (o • a) : Qt F') := by
        rw [Submodule.Quotient.mk_smul, ← algebraMap_smul E o, smul_smul, inv_mul_cancel₀ ho', one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/- English proof (translation)
Establish `hA2 : Λ.map ((γ : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) = Λ` using `hA.2`. Unfold `Formalism.HermitianLatticesTheory.gmap`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `q hq`. Take `⟨q0, hq0, rfl⟩` from `Submodule.mem_map.1 hq`.

Take `⟨a, ha, rfl⟩` from `(mem_Lb F' Λ).1 hq0`. Use `(mem_Lb F' Λ).2 ⟨γU F' γ hU a, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[γU_coe]`. Establish `h1 : γ (a : S.V) ∈ Λ.map ((γ : S.V →ₗ[E] S.V).restrictScalars (𝓞 E))` using `⟨a, ha, rfl⟩`. Rewrite `h1` using `[hA2]`. Then use the resulting hypothesis.

Introduce `q hq`. Take `⟨a, ha, rfl⟩` from `(mem_Lb F' Λ).1 hq`. Establish `h1 : (a : S.V) ∈ Λ.map ((γ : S.V →ₗ[E] S.V).restrictScalars (𝓞 E))`. Rewrite using `[hA2]`. Conclude with `ha`.

Take `⟨b, hb, hba⟩` from `Submodule.mem_map.1 h1`. Establish `hba' : γ b = (a : S.V)` using `hba`. Establish `hbU : b ∈ Uo F'` using `(hU b).1 (by rw [hba']; exact a.2)`. Use `Submodule.mem_map.2 ⟨Submodule.Quotient.mk ⟨b, hbU⟩, (mem_Lb F' Λ).2 ⟨⟨b, hbU⟩, hb, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show γQ F' γ hU hX (Submodule.Quotient.mk ⟨b, hbU⟩) = Submodule.Quotient.mk a`.

Rewrite using `[γQ_mk]`. Use `congr 1`. Use `ext`. Rewrite using `[γU_coe]`. Conclude with `hba'`.
-/
theorem γQ_Lb {T' : E} (F' : LFlag S r T') (Λ : Submodule (𝓞 E) S.V) (γ : S.V ≃ₗ[E] S.V)
    (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F') (hX : ∀ v, γ v ∈ Xsp F' ↔ v ∈ Xsp F') (hA : IsAutLam S Λ γ) :
    Formalism.HermitianLatticesTheory.gmap (γQ F' γ hU hX) (Lb F' Λ) = Lb F' Λ := by
  have hA2 : Λ.map ((γ : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) = Λ := hA.2
  unfold Formalism.HermitianLatticesTheory.gmap
  apply le_antisymm
  · intro q hq
    obtain ⟨q0, hq0, rfl⟩ := Submodule.mem_map.1 hq
    obtain ⟨a, ha, rfl⟩ := (mem_Lb F' Λ).1 hq0
    refine (mem_Lb F' Λ).2 ⟨γU F' γ hU a, ?_, rfl⟩
    rw [γU_coe]
    have h1 : γ (a : S.V) ∈ Λ.map ((γ : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) := ⟨a, ha, rfl⟩
    rwa [hA2] at h1
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := (mem_Lb F' Λ).1 hq
    have h1 : (a : S.V) ∈ Λ.map ((γ : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) := by
      rw [hA2]
      exact ha
    obtain ⟨b, hb, hba⟩ := Submodule.mem_map.1 h1
    have hba' : γ b = (a : S.V) := hba
    have hbU : b ∈ Uo F' := (hU b).1 (by rw [hba']; exact a.2)
    refine Submodule.mem_map.2 ⟨Submodule.Quotient.mk ⟨b, hbU⟩, (mem_Lb F' Λ).2 ⟨⟨b, hbU⟩, hb, rfl⟩, ?_⟩
    show γQ F' γ hU hX (Submodule.Quotient.mk ⟨b, hbU⟩) = Submodule.Quotient.mk a
    rw [γQ_mk]
    congr 1
    ext
    rw [γU_coe]
    exact hba'

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.gmap`. Rewrite using `[← Submodule.map_comp]`. Use `first`. Consider the case `rfl`. Consider the case `(congr 1)`.
-/
theorem gmap_mul' {T' : E} (F' : LFlag S r T') (a b : Qt F' ≃ₗ[E] Qt F') (L : Submodule (𝓞 E) (Qt F')) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  first
    | rfl
    | (congr 1)

/- English proof (translation)
Establish `hc : star (2 / ((T' : ℕ) : E)) = 2 / ((T' : ℕ) : E)`. Rewrite using `[star_div₀, star_natCast, star_ofNat]`. Establish `hfin` using `Formalism.HermitianLatticesTheory.autFinite E (Qt F') (hQ F' (2 / ((T' : ℕ) : E))) (hQ_symm F' _ hc) (hQ_trace_pos F' hT hτ hpos) (Lb F' Λ) (Lb_lattice F' Λ hΛ)`. Establish `hmem : ∀ k : ℕ, γQ F' γ hU hX ^ k ∈ {g | g ∈ Formalism.HermitianLatticesTheory.isom (hQ F' (2 / ((T' : ℕ) : E))) ∧ Formalism.HermitianLatticesTheory.gmap g (Lb F' Λ) = Lb F' Λ}`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero`. Use `⟨Subgroup.one_mem _, ?_⟩` and prove the remaining obligations. Unfold `Formalism.HermitianLatticesTheory.gmap`. Use extensionality with `q`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Use `⟨Subgroup.pow_mem _ (γQ_isom F' γ hU hX hA.1 hz _) _, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, gmap_mul', γQ_Lb F' Λ γ hU hX hA, ih.2]`. Take `⟨m, n, hmn, he⟩` from `hfin.exists_lt_map_eq_of_forall_mem hmem`.

Use `⟨n - m, Nat.sub_pos_of_lt hmn, ?_⟩` and prove the remaining obligations. Establish `h1 : γQ F' γ hU hX ^ m * γQ F' γ hU hX ^ (n - m) = γQ F' γ hU hX ^ m * 1`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hmn.le, mul_one, he]`. Conclude with `mul_left_cancel h1`.
-/
theorem γQ_finOrd {T' : ℕ} (F' : LFlag S r ((T' : ℕ) : E)) (hT : 0 < T')
    (hτ : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    (hpos : ∀ τ : E →+* ℂ, ∀ w ∈ orth S (Xplus F'), w ∉ Xsp F' → 0 < (τ (S.hT w w)).re)
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (γ : S.V ≃ₗ[E] S.V) (hA : IsAutLam S Λ γ)
    (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F') (hX : ∀ v, γ v ∈ Xsp F' ↔ v ∈ Xsp F')
    (hz : γ F'.fl.z = F'.fl.z) :
    ∃ n : ℕ, 0 < n ∧ γQ F' γ hU hX ^ n = 1 := by
  have hc : star (2 / ((T' : ℕ) : E)) = 2 / ((T' : ℕ) : E) := by
    rw [star_div₀, star_natCast, star_ofNat]
  have hfin := Formalism.HermitianLatticesTheory.autFinite E (Qt F') (hQ F' (2 / ((T' : ℕ) : E))) (hQ_symm F' _ hc)
    (hQ_trace_pos F' hT hτ hpos) (Lb F' Λ) (Lb_lattice F' Λ hΛ)
  have hmem : ∀ k : ℕ, γQ F' γ hU hX ^ k ∈ {g | g ∈ Formalism.HermitianLatticesTheory.isom (hQ F' (2 / ((T' : ℕ) : E))) ∧
      Formalism.HermitianLatticesTheory.gmap g (Lb F' Λ) = Lb F' Λ} := by
    intro k
    induction k with
    | zero =>
      refine ⟨Subgroup.one_mem _, ?_⟩
      unfold Formalism.HermitianLatticesTheory.gmap
      ext q
      simp
    | succ k ih =>
      refine ⟨Subgroup.pow_mem _ (γQ_isom F' γ hU hX hA.1 hz _) _, ?_⟩
      rw [pow_succ, gmap_mul', γQ_Lb F' Λ γ hU hX hA, ih.2]
  obtain ⟨m, n, hmn, he⟩ := hfin.exists_lt_map_eq_of_forall_mem hmem
  refine ⟨n - m, Nat.sub_pos_of_lt hmn, ?_⟩
  have h1 : γQ F' γ hU hX ^ m * γQ F' γ hU hX ^ (n - m) = γQ F' γ hU hX ^ m * 1 := by
    rw [← pow_add, Nat.add_sub_cancel' hmn.le, mul_one, he]
  exact mul_left_cancel h1

end Q3

end PI.UnitaryGroupMassFormula.BetaModX
