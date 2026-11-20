import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.TensLiftSelf

noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Char

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

def stabGLHat (Λ : Set (Fin n → E)) : Set (GL (Fin n) (Af F ⊗[F] E)) :=
  {g | (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ matStab (latHat (F := F) Λ) ∧
    ((g⁻¹ : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ matStab (latHat (F := F) Λ)}

/- English proof (translation)
Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `loc_of_matStab Λ hg.1 v hy`. Introduce `hy`.

Establish `hy' : ((g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).map (tensMap (E` using `E) (evalV F v))) *ᵥ y ∈ latLoc (E := E) v Λ := hy`. Establish `h` using `loc_of_matStab Λ hg.2 v hy'`. Rewrite `h` using `[Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem mem_Kloc_of (Λ : Set (Fin n → E)) {g : GL (Fin n) (Af F ⊗[F] E)} (hg : g ∈ stabGLHat Λ)
    (v : HeightOneSpectrum (𝓞 F)) : compV v g ∈ Kloc (E := E) v Λ := by
  intro y
  constructor
  · intro hy
    exact loc_of_matStab Λ hg.1 v hy
  · intro hy
    have hy' : ((g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).map (tensMap (E := E) (evalV F v))) *ᵥ y ∈
        latLoc (E := E) v Λ := hy
    have h := loc_of_matStab Λ hg.2 v hy'
    rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at h

/- English proof (translation)
Introduce `x hx v`. Rewrite using `[pv_mulVec]`. Conclude with `((hg v) (pv v x)).1 (hx v)`.
-/
theorem matStab_of_mem (Λ : Set (Fin n → E)) {g : GL (Fin n) (Af F ⊗[F] E)}
    (hg : ∀ v : HeightOneSpectrum (𝓞 F), compV v g ∈ Kloc (E := E) v Λ) :
    (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ matStab (latHat (F := F) Λ) := by
  intro x hx v
  rw [pv_mulVec]
  exact ((hg v) (pv v x)).1 (hx v)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `hg' : g⁻¹ ∈ Kf σ J Λ` using `(Kf σ J Λ).inv_mem hg`. Use `⟨matStab_of_mem Λ fun v => (Subgroup.mem_iInf.1 hg v), ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`.

Conclude with `matStab_of_mem Λ fun v => (Subgroup.mem_iInf.1 hg' v)`. Introduce `h`. Rewrite using `[Kf, Subgroup.mem_iInf]`. Introduce `v`. Conclude with `mem_Kloc_of Λ h v`.
-/
theorem kf_iff (Λ : Set (Fin n → E)) (g : HA (Af F) σ J) :
    g ∈ Kf σ J Λ ↔ incAf σ J g ∈ stabGLHat Λ := by
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ Kf σ J Λ := (Kf σ J Λ).inv_mem hg
    refine ⟨matStab_of_mem Λ fun v => (Subgroup.mem_iInf.1 hg v), ?_⟩
    rw [← map_inv]
    exact matStab_of_mem Λ fun v => (Subgroup.mem_iInf.1 hg' v)
  · intro h
    rw [Kf, Subgroup.mem_iInf]
    intro v
    exact mem_Kloc_of Λ h v

end Char

def LatHatOpen : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.span E (L : Set (Fin n → E)) = ⊤ → L.FG →
    IsOpen (latHat (F := F) (L : Set (Fin n → E)))

def LatHatCompact : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.span E (L : Set (Fin n → E)) = ⊤ → L.FG →
    IsCompact (latHat (F := F) (L : Set (Fin n → E)))

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[pv, ratV, Algebra.smul_def, tensMap, inclR]`. Simplify using `[pv, ratV, h, tensMap, inclR]`.
-/
theorem pv_intSmul_single (v : HeightOneSpectrum (𝓞 F)) (N : ℤ) (j : Fin n) :
    pv v ((N : F) • (Pi.single j 1 : Fin n → Af F ⊗[F] E)) = ratV (F := F) (Fv F v) (N • (Pi.single j (1 : E) : Fin n → E)) := by
  classical
  funext i
  by_cases h : i = j
  · subst h
    simp [pv, ratV, Algebra.smul_def, tensMap, inclR]
  · simp [pv, ratV, h, tensMap, inclR]

/- English proof (translation)
Introduce `v`. Rewrite using `[pv_intSmul_single]`. Conclude with `Submodule.subset_span ⟨_, hN j, rfl⟩`.
-/
theorem hcol_hat (L : Submodule (𝓞 E) (Fin n → E)) {N : ℤ}
    (hN : ∀ j : Fin n, N • (Pi.single j (1 : E) : Fin n → E) ∈ L) (j : Fin n) :
    (N : F) • (Pi.single j 1 : Fin n → Af F ⊗[F] E) ∈ latHat (F := F) (L : Set (Fin n → E)) := by
  intro v
  rw [pv_intSmul_single]
  exact Submodule.subset_span ⟨_, hN j, rfl⟩

/- English proof (translation)
Use `set M := latHat (F := F) (L : Set (Fin n → E))`. Establish `hMcl : IsClosed M` using `hc.isClosed`. Take `⟨N, hN0, hNmem⟩` from `exists_common_mult L hL (fun j : Fin n => (Pi.single j (1 : E) : Fin n → E))`. Establish `hN : (N : F) ≠ 0` using `Int.cast_ne_zero.mpr hN0`. Establish `hSc` using `isCompact_matStab (K := F) hc hMcl (N : F) hN (hcol_hat L hNmem)`.

Establish `e : stabGLHat (F` using `F) (L : Set (Fin n → E)) = Units.embedProduct _ ⁻¹' (matStab M ×ˢ (MulOpposite.op '' matStab M)) := by`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, ⟨_, h2, rfl⟩⟩`.

Introduce and unpack `⟨h1, y, hy, hyg⟩`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `hy' : y = (((g⁻¹ : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)))` using `MulOpposite.op_injective hyg`. Rewrite `hy` using `[hy']`. Then use the resulting hypothesis. Rewrite using `[e]`.

Conclude with `Units.isClosedEmbedding_embedProduct.isCompact_preimage (hSc.prod (hSc.image MulOpposite.continuous_op))`.
-/
theorem isCompact_stabGLHat (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hc : IsCompact (latHat (F := F) (L : Set (Fin n → E)))) :
    IsCompact (stabGLHat (F := F) (L : Set (Fin n → E))) := by
  classical
  set M := latHat (F := F) (L : Set (Fin n → E))
  have hMcl : IsClosed M := hc.isClosed
  obtain ⟨N, hN0, hNmem⟩ := exists_common_mult L hL (fun j : Fin n => (Pi.single j (1 : E) : Fin n → E))
  have hN : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  have hSc := isCompact_matStab (K := F) hc hMcl (N : F) hN (hcol_hat L hNmem)
  have e : stabGLHat (F := F) (L : Set (Fin n → E)) =
      Units.embedProduct _ ⁻¹' (matStab M ×ˢ (MulOpposite.op '' matStab M)) := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ⟨_, h2, rfl⟩⟩
    · rintro ⟨h1, y, hy, hyg⟩
      refine ⟨h1, ?_⟩
      have hy' : y = (((g⁻¹ : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))) :=
        MulOpposite.op_injective hyg
      rwa [hy'] at hy
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hSc.prod (hSc.image MulOpposite.continuous_op))

/- English proof (translation)
Establish `hS` using `isOpen_matStab hc ho`. Conclude with `(hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)`.
-/
theorem isOpen_stabGLHat (L : Submodule (𝓞 E) (Fin n → E))
    (hc : IsCompact (latHat (F := F) (L : Set (Fin n → E))))
    (ho : IsOpen (latHat (F := F) (L : Set (Fin n → E)))) :
    IsOpen (stabGLHat (F := F) (L : Set (Fin n → E))) := by
  have hS := isOpen_matStab hc ho
  exact (hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)

end Glob

end MassDataMassesW.KCptW

namespace MassDataMassesW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub KCptW

/- English proof (translation)
Introduce `D X`. Establish `: FiniteDimensional X.B.I.F X.B.I.E` using `Module.Finite.of_restrictScalars_finite ℚ _ _`. Establish `hMo` using `hO (F := X.B.I.F) X.B.I.L X.B.I.L_span X.B.I.L_fg`. Establish `hMc` using `hC (F := X.B.I.F) X.B.I.L X.B.I.L_span X.B.I.L_fg`. Establish `eK : (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) = incAf X.B.I.cm.sig X.B.I.J ⁻¹' stabGLHat (F` using `X.B.I.F) (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by`.

Use extensionality with `g`. Conclude with `kf_iff X.B.I.cm.sig X.B.I.J _ g`. Establish `hinc : Continuous (incAf X.B.I.cm.sig X.B.I.J)` using `continuous_subtype_val`. Rewrite using `[eK]`. Use `⟨?_, (isOpen_stabGLHat X.B.I.L hMc hMo).preimage hinc⟩` and prove the remaining obligations.

Conclude with `(PI.AdicCompletionValuation.isClosed_HR (Af X.B.I.F) X.B.I.cm.sig X.B.I.J).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_stabGLHat X.B.I.L X.B.I.L_span hMc)`.
-/
theorem kCompactOpen_of (hO : LatHatOpen) (hC : LatHatCompact) : KCompactOpen := by
  intro D X
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have hMo := hO (F := X.B.I.F) X.B.I.L X.B.I.L_span X.B.I.L_fg
  have hMc := hC (F := X.B.I.F) X.B.I.L X.B.I.L_span X.B.I.L_fg
  have eK : (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) =
      incAf X.B.I.cm.sig X.B.I.J ⁻¹' stabGLHat (F := X.B.I.F) (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    ext g
    exact kf_iff X.B.I.cm.sig X.B.I.J _ g
  have hinc : Continuous (incAf X.B.I.cm.sig X.B.I.J) := continuous_subtype_val
  rw [eK]
  refine ⟨?_, (isOpen_stabGLHat X.B.I.L hMc hMo).preimage hinc⟩
  exact (PI.AdicCompletionValuation.isClosed_HR (Af X.B.I.F) X.B.I.cm.sig X.B.I.J).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_stabGLHat X.B.I.L X.B.I.L_span hMc)

end MassDataMassesW
