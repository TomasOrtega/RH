import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DecompOrth

variable {D : D7}

/- English proof (translation)
Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `u hu`. Establish `hu' : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i : (VS D).V)`. Use `congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`.

Simplify using `only [Submodule.coe_smul] at this`. Conclude with `this.symm`. Rewrite using `[hu', map_sum]`. Simplify using `[hy]`.
-/
theorem mem_orth_of_basis {n : ℕ} (U : Submodule D.host.E (VS D).V)
    (b : Module.Basis (Fin n) D.host.E U) (y : (VS D).V)
    (hy : ∀ i, (VS D).hT (b i : (VS D).V) y = 0) : y ∈ orth (VS D) U := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u hu
  have hu' : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i : (VS D).V) := by
    have := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this.symm
  rw [hu', map_sum]
  simp [hy]

/- English proof (translation)
Set `b` to `Module.finBasis D.host.E U`. Set `L : U →ₗ[D.host.E] (Fin (Module.finrank D.host.E U) → D.host.E)` to `LinearMap.pi (fun i => ((VS D).hT (b i : (VS D).V)).comp U.subtype)`. Establish `hinj : Function.Injective L`. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `y hy`.

Rewrite `hy` using `[LinearMap.mem_ker]`. Establish `hy' : ∀ i, (VS D).hT (b i : (VS D).V) y = 0` using `fun i => congrFun hy i`. Establish `hmem : (y : (VS D).V) ∈ U ⊓ orth (VS D) U` using `⟨y.2, mem_orth_of_basis U b y hy'⟩`. Rewrite `hmem` using `[hU]`. Conclude with `Subtype.ext ((Submodule.mem_bot _).1 hmem)`.

Establish `hsurj : Function.Surjective L` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj`. Take `⟨y, hy⟩` from `hsurj (fun i => (VS D).hT (b i : (VS D).V) x)`. Use `⟨x - y, mem_orth_of_basis U b _ (fun i => ?_), y, y.2, by abel⟩` and prove the remaining obligations. Use `congrFun hy i` as an intermediate fact. Simplify using `only [L, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this`.

Rewrite using `[map_sub, this, sub_self]`.
-/
theorem exists_decomp (U : Submodule D.host.E (VS D).V) (hU : U ⊓ orth (VS D) U = ⊥)
    (x : (VS D).V) : ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b := by
  let b := Module.finBasis D.host.E U
  let L : U →ₗ[D.host.E] (Fin (Module.finrank D.host.E U) → D.host.E) :=
    LinearMap.pi (fun i => ((VS D).hT (b i : (VS D).V)).comp U.subtype)
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hy' : ∀ i, (VS D).hT (b i : (VS D).V) y = 0 := fun i => congrFun hy i
    have hmem : (y : (VS D).V) ∈ U ⊓ orth (VS D) U := ⟨y.2, mem_orth_of_basis U b y hy'⟩
    rw [hU] at hmem
    exact Subtype.ext ((Submodule.mem_bot _).1 hmem)
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨y, hy⟩ := hsurj (fun i => (VS D).hT (b i : (VS D).V) x)
  refine ⟨x - y, mem_orth_of_basis U b _ (fun i => ?_), y, y.2, by abel⟩
  have := congrFun hy i
  simp only [L, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [map_sub, this, sub_self]

/- English proof (translation)
Introduce `h`. Take `⟨α, hα0, hα⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h`. Apply `hα0` to reduce the goal to its premises. Establish `hy : ∀ i, (VS D).hT (b i : (VS D).V) (((∑ j, α j • b j : U)) : (VS D).V) = 0`. Introduce `i`.

Use `congrFun hα i` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this`. Rewrite using `[Submodule.coe_sum, map_sum]`. Simplify `this` using `[mul_comm]`. Establish `hmem : ((∑ j, α j • b j : U) : (VS D).V) ∈ U ⊓ orth (VS D) U` using `⟨Subtype.prop _, mem_orth_of_basis U b _ hy⟩`.

Rewrite `hmem` using `[hU, Submodule.mem_bot]`. Establish `h0 : ∑ j, α j • b j = 0` using `Subtype.ext hmem`. Use function extensionality and compare the values at `j`. Conclude with `Fintype.linearIndependent_iff.1 b.linearIndependent α h0 j`.
-/
theorem gram_det_ne_zero {n : ℕ} (U : Submodule D.host.E (VS D).V) (hU : U ⊓ orth (VS D) U = ⊥)
    (b : Module.Basis (Fin n) D.host.E U) :
    (Matrix.of fun i j => (VS D).hT (b i : (VS D).V) (b j : (VS D).V)).det ≠ 0 := by
  intro h
  obtain ⟨α, hα0, hα⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hα0
  have hy : ∀ i, (VS D).hT (b i : (VS D).V) (((∑ j, α j • b j : U)) : (VS D).V) = 0 := by
    intro i
    have := congrFun hα i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [Submodule.coe_sum, map_sum]
    simpa [mul_comm] using this
  have hmem : ((∑ j, α j • b j : U) : (VS D).V) ∈ U ⊓ orth (VS D) U :=
    ⟨Subtype.prop _, mem_orth_of_basis U b _ hy⟩
  rw [hU, Submodule.mem_bot] at hmem
  have h0 : ∑ j, α j • b j = 0 := Subtype.ext hmem
  funext j
  exact Fintype.linearIndependent_iff.1 b.linearIndependent α h0 j

end GlobalTheory.DecompOrth

namespace GlobalTheory.DecompOrth

variable {D : D7}

noncomputable def formLeft (Z : LocDat D) (p : PlF D) (w : Vp D p) : Vp D p →ₗ[(D.s.atP p).Ep] (D.s.atP p).Ep where
  toFun v := LocFacts₂ Z.M p v w
  map_add' x y := (locH Z p).h_add_left x y w
  map_smul' a x := (locH Z p).h_smul_left a x w

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem formLeft_apply (Z : LocDat D) (p : PlF D) (w v : Vp D p) :
    formLeft Z p w v = LocFacts₂ Z.M p v w := rfl

/- English proof (translation)
Set `b` to `Module.finBasis D.host.E U`. Establish `hspan : Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) ≤ Submodule.span (D.s.atP p).Ep (Set.range fun j => baseChange₂ D p (b j : (VS D).V))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Establish `hu' : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i : (VS D).V)`.

Use `congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at this`. Conclude with `this.symm`. Rewrite using `[hu', map_sum]`.

Use `Submodule.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[baseChange_smul₂]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Take `⟨β, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 (hspan hv)`. Use `set G := Matrix.of fun i j => (VS D).hT (b i : (VS D).V) (b j : (VS D).V) with hGdef`.

Use `set A := G.map (D.s.atP p).ιE with hA`. Establish `hAβ : Matrix.mulVec A β = 0`. Use function extensionality and compare the values at `i`. Establish `h1` using `horth (b i) (b i).2`. Establish `h2 : LocFacts₂ Z.M p (∑ j, β j • baseChange₂ D p (b j : (VS D).V)) (baseChange₂ D p (b i : (VS D).V)) = formLeft Z p (baseChange₂ D p (b i : (VS D).V)) (∑ j, β j • baseChange₂ D p (b j : (VS D).V))` using `rfl`.

Rewrite `h1` using `[h2, map_sum]`. Simplify using `only [map_smul, smul_eq_mul] at h1`. Simplify using `only [formLeft_apply, baseChangeAt_form Z.M p (Z.hcj p), brS] at h1`. Simplify using `only [Matrix.mulVec, dotProduct, hA, hGdef, Matrix.map_apply, Matrix.of_apply, Pi.zero_apply]`. Simplify `h1` using `[mul_comm]`.

Establish `hdet : IsUnit A.det`. Rewrite using `[hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(isUnit_iff_ne_zero.2 (gram_det_ne_zero U hU b)).map _`. Establish `hβ : β = 0`. Use `congrArg (fun w => Matrix.mulVec A⁻¹ w) hAβ` as an intermediate fact.

Simplify using `only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec, Matrix.mulVec_zero] at this`. Conclude with `this`. Simplify using `[hβ]`.
-/
theorem eq_zero_of_local_orth (U : Submodule D.host.E (VS D).V) (hU : U ⊓ orth (VS D) U = ⊥)
    (Z : LocDat D) (p : PlF D) (v : Vp D p)
    (hv : v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)))
    (horth : ∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) : v = 0 := by
  let b := Module.finBasis D.host.E U
  have hspan : Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) ≤
      Submodule.span (D.s.atP p).Ep (Set.range fun j => baseChange₂ D p (b j : (VS D).V)) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i : (VS D).V) := by
      have := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    rw [hu', map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [baseChange_smul₂]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hspan hv)
  set G := Matrix.of fun i j => (VS D).hT (b i : (VS D).V) (b j : (VS D).V) with hGdef
  set A := G.map (D.s.atP p).ιE with hA
  have hAβ : Matrix.mulVec A β = 0 := by
    funext i
    have h1 := horth (b i) (b i).2
    have h2 : LocFacts₂ Z.M p (∑ j, β j • baseChange₂ D p (b j : (VS D).V)) (baseChange₂ D p (b i : (VS D).V)) =
        formLeft Z p (baseChange₂ D p (b i : (VS D).V)) (∑ j, β j • baseChange₂ D p (b j : (VS D).V)) := rfl
    rw [h2, map_sum] at h1
    simp only [map_smul, smul_eq_mul] at h1
    simp only [formLeft_apply, baseChangeAt_form Z.M p (Z.hcj p), brS] at h1
    simp only [Matrix.mulVec, dotProduct, hA, hGdef, Matrix.map_apply, Matrix.of_apply, Pi.zero_apply]
    simpa [mul_comm] using h1
  have hdet : IsUnit A.det := by
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 (gram_det_ne_zero U hU b)).map _
  have hβ : β = 0 := by
    have := congrArg (fun w => Matrix.mulVec A⁻¹ w) hAβ
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  simp [hβ]

end GlobalTheory.DecompOrth

/- English proof (translation)
Introduce `_ U hU` and use `⟨GlobalTheory.DecompOrth.exists_decomp U hU, fun Z p v hv horth => GlobalTheory.DecompOrth.eq_zero_of_local_orth U hU Z p v hv horth⟩`.
-/
theorem GlobalTheory.decomp_orth_complement : ∀ (D : D7) (U : Submodule D.host.E (VS D).V), U ⊓ orth (VS D) U = ⊥ → (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) ∧ ∀ (Z : LocDat D) (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) → (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0 :=
  fun _ U hU => ⟨GlobalTheory.DecompOrth.exists_decomp U hU,
    fun Z p v hv horth => GlobalTheory.DecompOrth.eq_zero_of_local_orth U hU Z p v hv horth⟩
