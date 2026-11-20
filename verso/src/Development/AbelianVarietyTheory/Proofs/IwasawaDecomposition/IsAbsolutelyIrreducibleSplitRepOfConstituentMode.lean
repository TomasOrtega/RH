import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleMatrixRepIsInternalIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrSubOfIsIrrSubMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixSystemNonzeroSolutionDescendsStatement
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory.SplitCrit

variable {k L : Type} [Field k] [Field L]

abbrev ext (f : k →+* L) {a : ℕ} (W : Submodule k (Fin a → k)) : Submodule L (Fin a → L) :=
  Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec f M v i).symm`.
-/
theorem map_mulVec_comp (f : k →+* L) {m n : ℕ} (M : Matrix (Fin m) (Fin n) k) (v : Fin n → k) :
    (M.map f).mulVec (f ∘ v) = f ∘ M.mulVec v := by
  funext i; exact (RingHom.map_mulVec f M v i).symm

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Simplify using `only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]`. Rewrite using `[map_mulVec_comp]`. Conclude with `Submodule.subset_span ⟨_, h v hv, rfl⟩`.
-/
theorem ext_le_comap (f : k →+* L) {m n : ℕ} (M : Matrix (Fin m) (Fin n) k)
    (U : Submodule k (Fin n → k)) (U' : Submodule k (Fin m → k)) (h : ∀ v ∈ U, M.mulVec v ∈ U') :
    ext f U ≤ (ext f U').comap (M.map f).mulVecLin := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, hv, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
  rw [map_mulVec_comp]
  exact Submodule.subset_span ⟨_, h v hv, rfl⟩

/- English proof (translation)
Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW`. Introduce `h`. Establish `: f ∘ v ∈ ext f W` using `Submodule.subset_span ⟨v, hv, rfl⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`. Apply `hv0` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Use `congrFun this i` as an intermediate fact. Simplify using `using this`.
-/
theorem ext_ne_bot (f : k →+* L) {a : ℕ} {W : Submodule k (Fin a → k)} (hW : W ≠ ⊥) : ext f W ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  intro h
  have : f ∘ v ∈ ext f W := Submodule.subset_span ⟨v, hv, rfl⟩
  rw [h, Submodule.mem_bot] at this
  apply hv0; funext i
  have := congrFun this i
  simpa using this

/- English proof (translation)
Set `e` to `Module.finBasis k W`. Establish `hle : ext f W ≤ Submodule.span L (Set.range fun i => f ∘ (e i : Fin a → k))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Establish `hv' : v = ∑ i, (e.repr ⟨v, hv⟩ i) • (e i : Fin a → k)`.

Use `congrArg Subtype.val (e.sum_repr ⟨v, hv⟩)` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at this`. Conclude with `this.symm`. Establish `: f ∘ v = ∑ i, f (e.repr ⟨v, hv⟩ i) • (f ∘ (e i : Fin a → k))` using `by conv_lhs => rw [hv']`.

Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, map_sum]`. Use `show f ∘ v ∈ _`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem finrank_ext_le (f : k →+* L) {a : ℕ} (W : Submodule k (Fin a → k)) :
    Module.finrank L (ext f W) ≤ Module.finrank k W := by
  let e := Module.finBasis k W
  have hle : ext f W ≤ Submodule.span L (Set.range fun i => f ∘ (e i : Fin a → k)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v = ∑ i, (e.repr ⟨v, hv⟩ i) • (e i : Fin a → k) := by
      have := congrArg Subtype.val (e.sum_repr ⟨v, hv⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have : f ∘ v = ∑ i, f (e.repr ⟨v, hv⟩ i) • (f ∘ (e i : Fin a → k)) := by
      conv_lhs => rw [hv']
      funext j
      simp [Finset.sum_apply, map_sum]
    show f ∘ v ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  calc Module.finrank L (ext f W)
      ≤ Module.finrank L (Submodule.span L (Set.range fun i => f ∘ (e i : Fin a → k))) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (Module.finrank k W)) := finrank_range_le_card _
    _ = Module.finrank k W := Fintype.card_fin _

/- English proof (translation)
Introduce `h`. Apply `hX` to reduce the goal to its premises. Use `Matrix.ext_of_mulVec_single fun i => ?_` and prove the remaining obligations. Establish `: X.mulVecLin (Pi.single i 1) ∈ LinearMap.range X.mulVecLin` using `LinearMap.mem_range_self _ _`. Rewrite `this` using `[h, Submodule.mem_bot, Matrix.mulVecLin_apply]`.

Rewrite using `[this, Matrix.zero_mulVec]`.
-/
theorem range_ne_bot {K : Type} [Field K] {m n : ℕ} {X : Matrix (Fin m) (Fin n) K} (hX : X ≠ 0) :
    LinearMap.range X.mulVecLin ≠ ⊥ := by
  intro h
  apply hX
  refine Matrix.ext_of_mulVec_single fun i => ?_
  have : X.mulVecLin (Pi.single i 1) ∈ LinearMap.range X.mulVecLin := LinearMap.mem_range_self _ _
  rw [h, Submodule.mem_bot, Matrix.mulVecLin_apply] at this
  rw [this, Matrix.zero_mulVec]

end GlobalTheory.SplitCrit

namespace GlobalTheory.SplitCrit

/- English proof (translation)
Introduce `k Γ L _ _ _ _ f a ρ hmod W hW`. Take `⟨hW0, hWi, hWmin⟩` from `hW`. Establish `hLi : IsInv (mapRep f ρ) (ext f W)` using `fun g v hv => ext_le_comap f (ρ g : Matrix (Fin a) (Fin a) k) W W (hWi g) hv`. Take `⟨V, hVle, hV⟩` from `GlobalTheory.SemisimpleDecomp.exists_irr_le hLi (ext_ne_bot f hW0)`. Take `⟨b, σ, C, hCinj, hCr, hCint⟩` from `hmod V hV`.

Take `⟨W', hc⟩` from `Submodule.exists_isCompl W`. Set `φ : (Fin a → k) →ₗ[k] (Fin a → k)` to `W'.subtype.comp (W'.projectionOnto W hc.symm)`. Establish `hφ : ∀ v, φ v = 0 ↔ v ∈ W`. Introduce `v`. Establish `hk` using `Submodule.ker_projectionOnto hc.symm`.

Simplify using `only [φ, LinearMap.comp_apply, Submodule.subtype_apply, ZeroMemClass.coe_eq_zero]`. Rewrite using `[← LinearMap.mem_ker, hk]`. Set `Q` to `LinearMap.toMatrix' φ`. Establish `hQ : ∀ v, Q.mulVec v = 0 ↔ v ∈ W` using `fun v => by`. Simplify using `only [Q, LinearMap.toMatrix'_mulVec]`.

Conclude with `hφ v`. Establish `hQL : ext f W ≤ LinearMap.ker (Q.map f).mulVecLin`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]`.

Rewrite using `[map_mulVec_comp, (hQ v).2 hv]`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `hQC : Q.map f * C = 0`. Use `Matrix.ext_of_mulVec_single fun j => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]`. Establish `: C.mulVec (Pi.single j 1) ∈ V` using `hCr ▸ LinearMap.mem_range_self C.mulVecLin _`. Use `hQL (hVle this)` as an intermediate fact. Simplify using `using this`. Establish `hC0 : C ≠ 0`.

Introduce `h`. Apply `hV.1` to reduce the goal to its premises. Rewrite using `[← hCr, h]`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Establish `hint : ∀ g, ((ρ g : Matrix (Fin a) (Fin a) k)).map f * C = C * ((σ g : Matrix (Fin b) (Fin b) k)).map f` using `fun g => hCint g`. Take `⟨X, hX0, hXint, hQX⟩` from `GlobalTheory.T.exists_ne_zero_intertwiner_of_map f (fun g => (ρ g : Matrix (Fin a) (Fin a) k)) (fun g => (σ g : Matrix (Fin b) (Fin b) k)) Q C hC0 hint hQC`. Establish `hXW : LinearMap.range X.mulVecLin ≤ W`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[← hQ, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQX, Matrix.zero_mulVec]`.

Establish `hXi : IsInv ρ (LinearMap.range X.mulVecLin)`. Introduce and unpack `g _ ⟨w, rfl⟩`. Use `⟨(σ g : Matrix (Fin b) (Fin b) k).mulVec w, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hXint g]`. Establish `hXeq : LinearMap.range X.mulVecLin = W` using `(hWmin _ hXW hXi).resolve_left (range_ne_bot hX0)`.

Establish `hWb : Module.finrank k W ≤ b`. Rewrite using `[← hXeq]`. Conclude with `(LinearMap.finrank_range_le _).trans (Module.finrank_fin_fun k).le`. Establish `hVb : Module.finrank L V = b`. Rewrite using `[← hCr, LinearMap.finrank_range_of_inj hCinj, Module.finrank_fin_fun]`.

Establish `hVeq : V = ext f W` using `Submodule.eq_of_le_of_finrank_le hVle ((finrank_ext_le f W).trans (hWb.trans hVb.ge))`. Establish `hV' : IsIrrSub (mapRep f ρ) (ext f W)` using `hVeq ▸ hV`. Conclude with `GlobalTheory.T.absIrrSub_of_isIrrSub_span_map f ρ W hWi hV'`.
-/
theorem splitRep_of_models : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), (∀ V, IsIrrSub (mapRep f ρ) V → ∃ (b : ℕ) (σ : Γ →* GL (Fin b) k) (C : Matrix (Fin a) (Fin b) L), Function.Injective C.mulVec ∧ LinearMap.range C.mulVecLin = V ∧ ∀ g, ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * C = C * ((mapRep f σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L)) → GlobalTheory.SplitCoef.SplitRep ρ := by
  intro k Γ L _ _ _ _ f a ρ hmod W hW
  obtain ⟨hW0, hWi, hWmin⟩ := hW

  have hLi : IsInv (mapRep f ρ) (ext f W) := fun g v hv =>
    ext_le_comap f (ρ g : Matrix (Fin a) (Fin a) k) W W (hWi g) hv
  obtain ⟨V, hVle, hV⟩ := GlobalTheory.SemisimpleDecomp.exists_irr_le hLi (ext_ne_bot f hW0)
  obtain ⟨b, σ, C, hCinj, hCr, hCint⟩ := hmod V hV

  obtain ⟨W', hc⟩ := Submodule.exists_isCompl W
  let φ : (Fin a → k) →ₗ[k] (Fin a → k) := W'.subtype.comp (W'.projectionOnto W hc.symm)
  have hφ : ∀ v, φ v = 0 ↔ v ∈ W := by
    intro v
    have hk := Submodule.ker_projectionOnto hc.symm
    simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply, ZeroMemClass.coe_eq_zero]
    rw [← LinearMap.mem_ker, hk]
  let Q := LinearMap.toMatrix' φ
  have hQ : ∀ v, Q.mulVec v = 0 ↔ v ∈ W := fun v => by
    simp only [Q, LinearMap.toMatrix'_mulVec]; exact hφ v

  have hQL : ext f W ≤ LinearMap.ker (Q.map f).mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rw [map_mulVec_comp, (hQ v).2 hv]
    funext i; simp
  have hQC : Q.map f * C = 0 := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
    have : C.mulVec (Pi.single j 1) ∈ V := hCr ▸ LinearMap.mem_range_self C.mulVecLin _
    have := hQL (hVle this)
    simpa using this
  have hC0 : C ≠ 0 := by
    intro h; apply hV.1; rw [← hCr, h]
    ext x; simp
  have hint : ∀ g, ((ρ g : Matrix (Fin a) (Fin a) k)).map f * C = C * ((σ g : Matrix (Fin b) (Fin b) k)).map f :=
    fun g => hCint g
  obtain ⟨X, hX0, hXint, hQX⟩ := GlobalTheory.T.exists_ne_zero_intertwiner_of_map f (fun g => (ρ g : Matrix (Fin a) (Fin a) k))
    (fun g => (σ g : Matrix (Fin b) (Fin b) k)) Q C hC0 hint hQC

  have hXW : LinearMap.range X.mulVecLin ≤ W := by
    rintro _ ⟨w, rfl⟩
    rw [← hQ, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQX, Matrix.zero_mulVec]
  have hXi : IsInv ρ (LinearMap.range X.mulVecLin) := by
    rintro g _ ⟨w, rfl⟩
    refine ⟨(σ g : Matrix (Fin b) (Fin b) k).mulVec w, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hXint g]
  have hXeq : LinearMap.range X.mulVecLin = W :=
    (hWmin _ hXW hXi).resolve_left (range_ne_bot hX0)
  have hWb : Module.finrank k W ≤ b := by
    rw [← hXeq]
    exact (LinearMap.finrank_range_le _).trans (Module.finrank_fin_fun k).le
  have hVb : Module.finrank L V = b := by
    rw [← hCr, LinearMap.finrank_range_of_inj hCinj, Module.finrank_fin_fun]
  have hVeq : V = ext f W :=
    Submodule.eq_of_le_of_finrank_le hVle ((finrank_ext_le f W).trans (hWb.trans hVb.ge))
  have hV' : IsIrrSub (mapRep f ρ) (ext f W) := hVeq ▸ hV
  exact GlobalTheory.T.absIrrSub_of_isIrrSub_span_map f ρ W hWi hV'

end GlobalTheory.SplitCrit
