import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.VmulCommEvPt

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def evM {ι : Type} (P : ι → ι → MvPolynomial (Vars L n) ℂ) (y : Vars L n → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => MvPolynomial.eval y (P i j)

/- English proof (translation)
Use extensionality with `i j`. Use `set g : Vars L n → MvPolynomial (Vars L n) ℂ := fun p => ∑ k, MvPolynomial.C (z (p.1, k, p.2.2)) * MvPolynomial.X (p.1, p.2.1, k) with hg`. Establish `hv : ∀ y' : Vars L n → ℂ, (fun p => MvPolynomial.eval y' (g p)) = vmul y' z`. Introduce `y'`. Use function extensionality and compare the values at `p`.

Simplify using `[hg, vmul, mul_comm]`. Establish `hF : ∀ y' : Vars L n → ℂ, MvPolynomial.eval y' (MvPolynomial.aeval g (P i j) - ∑ k, P i k * MvPolynomial.C (MvPolynomial.eval z (P k j))) = evM P (vmul y' z) i j - (evM P y' * evM P z) i j`. Introduce `y'`. Rewrite using `[map_sub, eval_aeval_eq, hv, map_sum]`. Simplify using `[evM, Matrix.mul_apply]`.

Establish `key` using `hd L n _ (fun γ₀ hγ => by rw [hF, hrat γ₀ hγ, sub_self]) y hy`. Rewrite `key` using `[hF]`. Conclude with `sub_eq_zero.1 key`.
-/
theorem mult_right (hd : DensStep) {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial (Vars L n) ℂ)
    (z : Vars L n → ℂ)
    (hrat : ∀ γ₀ ∈ GQ0 L n, evM P (vmul (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) z) =
      evM P (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) * evM P z)
    (y : Vars L n → ℂ) (hy : InV y) : evM P (vmul y z) = evM P y * evM P z := by
  ext i j
  set g : Vars L n → MvPolynomial (Vars L n) ℂ :=
    fun p => ∑ k, MvPolynomial.C (z (p.1, k, p.2.2)) * MvPolynomial.X (p.1, p.2.1, k) with hg
  have hv : ∀ y' : Vars L n → ℂ, (fun p => MvPolynomial.eval y' (g p)) = vmul y' z := by
    intro y'
    funext p
    simp [hg, vmul, mul_comm]
  have hF : ∀ y' : Vars L n → ℂ, MvPolynomial.eval y' (MvPolynomial.aeval g (P i j) -
      ∑ k, P i k * MvPolynomial.C (MvPolynomial.eval z (P k j))) =
      evM P (vmul y' z) i j - (evM P y' * evM P z) i j := by
    intro y'
    rw [map_sub, eval_aeval_eq, hv, map_sum]
    simp [evM, Matrix.mul_apply]
  have key := hd L n _ (fun γ₀ hγ => by rw [hF, hrat γ₀ hγ, sub_self]) y hy
  rw [hF] at key
  exact sub_eq_zero.1 key

/- English proof (translation)
Use extensionality with `i j`. Use `set g : Vars L n → MvPolynomial (Vars L n) ℂ := fun p => ∑ k, MvPolynomial.C (y (p.1, p.2.1, k)) * MvPolynomial.X (p.1, k, p.2.2) with hg`. Establish `hv : ∀ z' : Vars L n → ℂ, (fun p => MvPolynomial.eval z' (g p)) = vmul y z'`. Introduce `z'`. Use function extensionality and compare the values at `p`.

Simplify using `[hg, vmul]`. Establish `hF : ∀ z' : Vars L n → ℂ, MvPolynomial.eval z' (MvPolynomial.aeval g (P i j) - ∑ k, MvPolynomial.C (MvPolynomial.eval y (P i k)) * P k j) = evM P (vmul y z') i j - (evM P y * evM P z') i j`. Introduce `z'`. Rewrite using `[map_sub, eval_aeval_eq, hv, map_sum]`. Simplify using `[evM, Matrix.mul_apply]`.

Establish `key` using `hd L n _ (fun δ₀ hδ => by rw [hF, hrat δ₀ hδ, sub_self]) z hz`. Rewrite `key` using `[hF]`. Conclude with `sub_eq_zero.1 key`.
-/
theorem mult_left (hd : DensStep) {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial (Vars L n) ℂ)
    (y : Vars L n → ℂ)
    (hrat : ∀ δ₀ ∈ GQ0 L n, evM P (vmul y (ratPt (δ₀ : Matrix (Fin n) (Fin n) L))) =
      evM P y * evM P (ratPt (δ₀ : Matrix (Fin n) (Fin n) L)))
    (z : Vars L n → ℂ) (hz : InV z) : evM P (vmul y z) = evM P y * evM P z := by
  ext i j
  set g : Vars L n → MvPolynomial (Vars L n) ℂ :=
    fun p => ∑ k, MvPolynomial.C (y (p.1, p.2.1, k)) * MvPolynomial.X (p.1, k, p.2.2) with hg
  have hv : ∀ z' : Vars L n → ℂ, (fun p => MvPolynomial.eval z' (g p)) = vmul y z' := by
    intro z'
    funext p
    simp [hg, vmul]
  have hF : ∀ z' : Vars L n → ℂ, MvPolynomial.eval z' (MvPolynomial.aeval g (P i j) -
      ∑ k, MvPolynomial.C (MvPolynomial.eval y (P i k)) * P k j) =
      evM P (vmul y z') i j - (evM P y * evM P z') i j := by
    intro z'
    rw [map_sub, eval_aeval_eq, hv, map_sum]
    simp [evM, Matrix.mul_apply]
  have key := hd L n _ (fun δ₀ hδ => by rw [hF, hrat δ₀ hδ, sub_self]) z hz
  rw [hF] at key
  exact sub_eq_zero.1 key

/- English proof (translation)
Establish `hl : ∀ γ₀ ∈ GQ0 L n, ∀ z' : Vars L n → ℂ, InV z' → evM P (vmul (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) z') = evM P (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) * evM P z'`. Introduce `γ₀ hγ z' hz'`. Apply `mult_left hd P _ _ z' hz'` to reduce the goal to its premises. Introduce `δ₀ hδ`. Rewrite using `[← hrat γ₀ hγ δ₀ hδ]`.

Use `congr 1`. Use function extensionality and compare the values at `p`. Simplify using `[vmul, ratPt, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]`. Conclude with `mult_right hd P z (fun γ₀ hγ => hl γ₀ hγ z hz) y hy`.
-/
theorem mult_of_dens (hd : DensStep) {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial (Vars L n) ℂ)
    (hrat : ∀ γ₀ ∈ GQ0 L n, ∀ δ₀ ∈ GQ0 L n,
      evM P (ratPt ((γ₀ * δ₀ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) =
        evM P (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) * evM P (ratPt (δ₀ : Matrix (Fin n) (Fin n) L)))
    (y z : Vars L n → ℂ) (hy : InV y) (hz : InV z) : evM P (vmul y z) = evM P y * evM P z := by
  have hl : ∀ γ₀ ∈ GQ0 L n, ∀ z' : Vars L n → ℂ, InV z' →
      evM P (vmul (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) z') =
        evM P (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) * evM P z' := by
    intro γ₀ hγ z' hz'
    apply mult_left hd P _ _ z' hz'
    intro δ₀ hδ
    rw [← hrat γ₀ hγ δ₀ hδ]
    congr 1
    funext p
    simp [vmul, ratPt, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]
  exact mult_right hd P z (fun γ₀ hγ => hl γ₀ hγ z hz) y hy

/- English proof (translation)
Use extensionality with `i j`. Establish `hF : ∀ y' : Vars L n → ℂ, MvPolynomial.eval y' (P i j - ∑ l, ∑ k, MvPolynomial.C (C i k * C' l j) * P' k l) = evM P y' i j - (C * evM P' y' * C') i j`. Introduce `y'`. Rewrite using `[map_sub, map_sum]`. Simplify using `only [map_sum, map_mul, MvPolynomial.eval_C, evM, Matrix.of_apply, Matrix.mul_apply]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `key` using `hd L n _ (fun γ₀ hγ => by rw [hF, hrat γ₀ hγ, sub_self]) y hy`. Rewrite `key` using `[hF]`. Conclude with `sub_eq_zero.1 key`.
-/
theorem change_of_dens (hd : DensStep) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (P : ι → ι → MvPolynomial (Vars L n) ℂ) (P' : ι' → ι' → MvPolynomial (Vars L n) ℂ)
    (C : Matrix ι ι' ℂ) (C' : Matrix ι' ι ℂ)
    (hrat : ∀ γ₀ ∈ GQ0 L n, evM P (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) =
      C * evM P' (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) * C')
    (y : Vars L n → ℂ) (hy : InV y) : evM P y = C * evM P' y * C' := by
  ext i j
  have hF : ∀ y' : Vars L n → ℂ, MvPolynomial.eval y' (P i j -
      ∑ l, ∑ k, MvPolynomial.C (C i k * C' l j) * P' k l) = evM P y' i j - (C * evM P' y' * C') i j := by
    intro y'
    rw [map_sub, map_sum]
    simp only [map_sum, map_mul, MvPolynomial.eval_C, evM, Matrix.of_apply, Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have key := hd L n _ (fun γ₀ hγ => by rw [hF, hrat γ₀ hγ, sub_self]) y hy
  rw [hF] at key
  exact sub_eq_zero.1 key

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[toGQ, map_mul]`.
-/
theorem toGQ_mul (γ₀ δ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) (hδ : δ₀ ∈ GQ0 L n) :
    toGQ (γ₀ * δ₀) (Subgroup.mul_mem _ hγ hδ) = toGQ γ₀ hγ * toGQ δ₀ hδ := by
  apply Subtype.ext
  apply Subtype.ext
  simp [toGQ, map_mul]

/- English proof (translation)
Take `⟨g, hg, h⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)`. Conclude with `⟨g, hg, Subtype.ext (Subtype.ext h.symm)⟩`.
-/
theorem toGQ_surj (γ : GQ L n) : ∃ γ₀ : GL (Fin n) L, ∃ hγ : γ₀ ∈ GQ0 L n, γ = toGQ γ₀ hγ := by
  obtain ⟨g, hg, h⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  exact ⟨g, hg, Subtype.ext (Subtype.ext h.symm)⟩

/- English proof (translation)
Use `set R : Set a.W := Set.range fun γ : GQ L n => a.ρ γ x with hR`. Establish `hT : {w | ∃ γ : GQ L n, w = Matrix.mulVec (LinearMap.toMatrix b b (a.ρ γ)) (b.equivFun x)} = b.equivFun '' R`. Use extensionality with `w`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image, hR, Set.mem_range, exists_exists_eq_and]`. Establish `key : ∀ γ : GQ L n, b.equivFun (a.ρ γ x) = Matrix.mulVec (LinearMap.toMatrix b b (a.ρ γ)) (b.equivFun x)`.

Introduce `γ`. Rewrite using `[Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, rfl⟩`. Conclude with `⟨γ, key γ⟩`.

Introduce and unpack `⟨γ, rfl⟩`. Conclude with `⟨γ, key γ⟩`. Establish `hS : Submodule.span ℂ R = ⊤` using `by haveI : IsSimpleModule (MonoidAlgebra ℂ (GQ L n)) a.ρ.asModule := (Representation.irreducible_iff_isSimpleModule_asModule a.ρ).1 a.irr set m := a.ρ.asModuleEquiv.symm x with hm`. Establish `hm0 : m ≠ 0` using `(LinearEquiv.map_ne_zero_iff _).2 hx`. Establish `htop : Submodule.span (MonoidAlgebra ℂ (GQ L n)) {m} = ⊤` using `(IsSimpleOrder.eq_bot_or_eq_top _).resolve_left ((Submodule.span_singleton_eq_bot).not.2 hm0)`.

Establish `halg : ∀ r : MonoidAlgebra ℂ (GQ L n), a.ρ.asAlgebraHom r x ∈ Submodule.span ℂ R`. Introduce `r`. Proceed by induction on `r using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f g hf hg`.

Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `add_mem hf hg`. Consider the case `single g c`. Rewrite using `[Representation.asAlgebraHom_single, LinearMap.smul_apply]`. Conclude with `Submodule.smul_mem _ c (Submodule.subset_span ⟨g, rfl⟩)`.

Rewrite using `[eq_top_iff]`. Introduce `w _`. Establish `hw : a.ρ.asModuleEquiv.symm w ∈ Submodule.span (MonoidAlgebra ℂ (GQ L n)) {m}`. Rewrite using `[htop]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.1 hw`. Establish `e : w = a.ρ.asAlgebraHom r x`. Establish `h2` using `congrArg a.ρ.asModuleEquiv hr`. Rewrite `h2` using `[Representation.asModuleEquiv_map_smul, hm, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Conclude with `h2.symm`.

Rewrite using `[e]`. Conclude with `halg r`. Rewrite using `[hT]`. Establish `e2 : (b.equivFun : a.W → (ι → ℂ)) '' R = (b.equivFun.toLinearMap : a.W →ₗ[ℂ] (ι → ℂ)) '' R` using `rfl`. Rewrite using `[e2, Submodule.span_image, hS, Submodule.map_top, LinearMap.range_eq_top]`.

Conclude with `b.equivFun.surjective`.
-/
theorem span_orbit (a : AlgWt L n) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (x : a.W)
    (hx : x ≠ 0) :
    Submodule.span ℂ {w | ∃ γ : GQ L n, w = Matrix.mulVec (LinearMap.toMatrix b b (a.ρ γ)) (b.equivFun x)} = ⊤ := by
  classical
  set R : Set a.W := Set.range fun γ : GQ L n => a.ρ γ x with hR
  have hT : {w | ∃ γ : GQ L n, w = Matrix.mulVec (LinearMap.toMatrix b b (a.ρ γ)) (b.equivFun x)} =
      b.equivFun '' R := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_image, hR, Set.mem_range, exists_exists_eq_and]
    have key : ∀ γ : GQ L n, b.equivFun (a.ρ γ x) = Matrix.mulVec (LinearMap.toMatrix b b (a.ρ γ)) (b.equivFun x) := by
      intro γ
      rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨γ, key γ⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨γ, key γ⟩
  have hS : Submodule.span ℂ R = ⊤ := by
    haveI : IsSimpleModule (MonoidAlgebra ℂ (GQ L n)) a.ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule a.ρ).1 a.irr
    set m := a.ρ.asModuleEquiv.symm x with hm
    have hm0 : m ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hx
    have htop : Submodule.span (MonoidAlgebra ℂ (GQ L n)) {m} = ⊤ :=
      (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left ((Submodule.span_singleton_eq_bot).not.2 hm0)
    have halg : ∀ r : MonoidAlgebra ℂ (GQ L n), a.ρ.asAlgebraHom r x ∈ Submodule.span ℂ R := by
      intro r
      induction r using MonoidAlgebra.induction_linear with
      | zero => simp
      | add f g hf hg =>
        rw [map_add, LinearMap.add_apply]
        exact add_mem hf hg
      | single g c =>
        rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
        exact Submodule.smul_mem _ c (Submodule.subset_span ⟨g, rfl⟩)
    rw [eq_top_iff]
    intro w _
    have hw : a.ρ.asModuleEquiv.symm w ∈ Submodule.span (MonoidAlgebra ℂ (GQ L n)) {m} := by
      rw [htop]; trivial
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hw
    have e : w = a.ρ.asAlgebraHom r x := by
      have h2 := congrArg a.ρ.asModuleEquiv hr
      rw [Representation.asModuleEquiv_map_smul, hm, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply] at h2
      exact h2.symm
    rw [e]
    exact halg r
  rw [hT]
  have e2 : (b.equivFun : a.W → (ι → ℂ)) '' R = (b.equivFun.toLinearMap : a.W →ₗ[ℂ] (ι → ℂ)) '' R := rfl
  rw [e2, Submodule.span_image, hS, Submodule.map_top, LinearMap.range_eq_top]
  exact b.equivFun.surjective

end

end PI.UnitaryGroupMassFormula.HwConjInf
