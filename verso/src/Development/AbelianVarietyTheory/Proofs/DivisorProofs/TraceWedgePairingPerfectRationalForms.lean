import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD

/- English proof (translation)
Establish `hdet : ∀ v : Fin (p + q) → V, τ (ExteriorAlgebra.ιMulti K (p + q) v) = τ (ExteriorAlgebra.ιMulti K (p + q) b) * b.det v`. Introduce `v`. Establish `e` using `congrArg (fun f => f v) (AlternatingMap.eq_smul_basis_det b (τ.compAlternatingMap (ExteriorAlgebra.ιMulti K (p + q))))`. Simplify `e` using `[mul_comm]`. Establish `htop : ∀ U : Set.powersetCard (Fin (p + q)) (p + q), τ (ExteriorAlgebra.ιMulti_family K (p + q) b U) ≠ 0`.

Introduce `U`. Use `set e := Set.powersetCard.ofFinEmbEquiv.symm U`. Establish `hinj : Function.Injective e` using `e.injective`. Establish `hbij : Function.Bijective e` using `⟨hinj, Finite.injective_iff_surjective.1 hinj⟩`. Set `σ` to `Equiv.ofBijective e hbij`.

Establish `hb : (b ∘ e) = ⇑(b.reindex σ.symm)`. Use function extensionality and compare the values at `i`. Simplify using `[σ]`. Rewrite using `[ExteriorAlgebra.ιMulti_family, hdet, hb]`. Conclude with `mul_ne_zero hτ (b.isUnit_det _).ne_zero`.

Establish `hcoe : ∀ {n : ℕ} (I : Set.powersetCard (Fin (p + q)) n), ((Module.Basis.exteriorPower n b I : ⋀[K]^n V) : ExteriorAlgebra K V) = ExteriorAlgebra.ιMulti_family K n b I`. Introduce `n I`. Simplify using `[exteriorPower.basis_apply, exteriorPower.ιMulti_family, ExteriorAlgebra.ιMulti_family]`. Use `set B := Module.Basis.exteriorPower q b`. Use `set Y : ⋀[K]^q V := ⟨y, hy⟩`.

It suffices to establish `hY : B.repr Y = 0 by`. Establish `: Y = 0` using `B.repr.injective (by rw [hY, map_zero])`. Conclude with `congrArg Subtype.val this`. Use extensionality with `J`. Establish `hJc : (J.valᶜ : Finset (Fin (p + q))).card = p`.

Rewrite using `[Finset.card_compl, Fintype.card_fin, show (J.val).card = q from J.prop]`. Use linear arithmetic over natural numbers and integers. Set `Jc : Set.powersetCard (Fin (p + q)) p` to `⟨J.valᶜ, by simpa using hJc⟩`. Establish `hdisj : Disjoint Jc.val J.val` using `disjoint_compl_left`. Use `set a : ExteriorAlgebra K V := ExteriorAlgebra.ιMulti_family K p b Jc`.

Establish `ha : a ∈ ⋀[K]^p V`. Rewrite using `[show a = _ from (hcoe Jc).symm]`. Conclude with `(Module.Basis.exteriorPower p b Jc).2`. Establish `hy' : y = ∑ I, B.repr Y I • (ExteriorAlgebra.ιMulti_family K q b I)`. Use `congrArg Subtype.val (B.sum_repr Y)` as an intermediate fact.

Express the relevant statement in the definitionally equal form `(Y : ExteriorAlgebra K V) = _`. Rewrite using `[← this, Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, hcoe]`. Establish `key` using `h a ha`.

Rewrite `key` using `[hy', Finset.mul_sum, map_sum, Finset.sum_eq_single J]`. Rewrite `key` using `[mul_smul_comm, map_smul, ExteriorAlgebra.ιMulti_family_mul_of_disjoint _ _ _ _ hdisj, Units.smul_def, map_zsmul, smul_eq_mul]`. Break down `mul_eq_zero.1 key with h0 | h0` into its components or cases. Simplify using `using h0`. It suffices to derive a contradiction.

Apply the tactic sequence `rcases Int.units_eq_one_or (Set.powersetCard.permOfDisjoint hdisj).sign with hs | hs <;>`. Apply the tactic sequence `rw [hs] at h0 <;> simp at h0 <;> exact htop _ h0`. Introduce `I _ hI`. Rewrite using `[mul_smul_comm, ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint, smul_zero, map_zero]`. Introduce `hd`.

Apply `hI` to reduce the goal to its premises. Establish `hsub : I.val ⊆ J.val`. Introduce `i hi`. Assume the negation of the conclusion as `hj`. Conclude with `Finset.disjoint_left.1 hd (show i ∈ J.valᶜ from Finset.mem_compl.2 hj) hi`.

Establish `hle : J.val.card ≤ I.val.card`. Rewrite using `[show (I.val).card = q from I.prop, show (J.val).card = q from J.prop]`. Conclude with `Subtype.ext (Finset.eq_of_subset_of_card_le hsub hle)`. Introduce `hJ`. Conclude with `absurd (Finset.mem_univ J) hJ`.
-/
theorem wedge_pairing_sep {K V : Type} [Field K] [AddCommGroup V] [Module K V] {p q : ℕ}
    (b : Module.Basis (Fin (p + q)) K V) (τ : ExteriorAlgebra K V →ₗ[K] K)
    (hτ : τ (ExteriorAlgebra.ιMulti K (p + q) b) ≠ 0) (y : ExteriorAlgebra K V) (hy : y ∈ ⋀[K]^q V)
    (h : ∀ a ∈ ⋀[K]^p V, τ (a * y) = 0) : y = 0 := by
  classical
  have hdet : ∀ v : Fin (p + q) → V,
      τ (ExteriorAlgebra.ιMulti K (p + q) v) = τ (ExteriorAlgebra.ιMulti K (p + q) b) * b.det v := by
    intro v
    have e := congrArg (fun f => f v)
      (AlternatingMap.eq_smul_basis_det b (τ.compAlternatingMap (ExteriorAlgebra.ιMulti K (p + q))))
    simpa [mul_comm] using e
  have htop : ∀ U : Set.powersetCard (Fin (p + q)) (p + q),
      τ (ExteriorAlgebra.ιMulti_family K (p + q) b U) ≠ 0 := by
    intro U
    set e := Set.powersetCard.ofFinEmbEquiv.symm U
    have hinj : Function.Injective e := e.injective
    have hbij : Function.Bijective e := ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
    let σ := Equiv.ofBijective e hbij
    have hb : (b ∘ e) = ⇑(b.reindex σ.symm) := by
      funext i; simp [σ]
    rw [ExteriorAlgebra.ιMulti_family, hdet, hb]
    exact mul_ne_zero hτ (b.isUnit_det _).ne_zero
  have hcoe : ∀ {n : ℕ} (I : Set.powersetCard (Fin (p + q)) n),
      ((Module.Basis.exteriorPower n b I : ⋀[K]^n V) : ExteriorAlgebra K V) =
        ExteriorAlgebra.ιMulti_family K n b I := by
    intro n I
    simp [exteriorPower.basis_apply, exteriorPower.ιMulti_family, ExteriorAlgebra.ιMulti_family]
  set B := Module.Basis.exteriorPower q b
  set Y : ⋀[K]^q V := ⟨y, hy⟩
  suffices hY : B.repr Y = 0 by
    have : Y = 0 := B.repr.injective (by rw [hY, map_zero])
    exact congrArg Subtype.val this
  ext J
  have hJc : (J.valᶜ : Finset (Fin (p + q))).card = p := by
    rw [Finset.card_compl, Fintype.card_fin, show (J.val).card = q from J.prop]; omega
  let Jc : Set.powersetCard (Fin (p + q)) p := ⟨J.valᶜ, by simpa using hJc⟩
  have hdisj : Disjoint Jc.val J.val := disjoint_compl_left
  set a : ExteriorAlgebra K V := ExteriorAlgebra.ιMulti_family K p b Jc
  have ha : a ∈ ⋀[K]^p V := by
    rw [show a = _ from (hcoe Jc).symm]; exact (Module.Basis.exteriorPower p b Jc).2
  have hy' : y = ∑ I, B.repr Y I • (ExteriorAlgebra.ιMulti_family K q b I) := by
    have := congrArg Subtype.val (B.sum_repr Y)
    change (Y : ExteriorAlgebra K V) = _
    rw [← this, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Submodule.coe_smul, hcoe]
  have key := h a ha
  rw [hy', Finset.mul_sum, map_sum, Finset.sum_eq_single J] at key
  · rw [mul_smul_comm, map_smul, ExteriorAlgebra.ιMulti_family_mul_of_disjoint _ _ _ _ hdisj,
      Units.smul_def, map_zsmul, smul_eq_mul] at key
    rcases mul_eq_zero.1 key with h0 | h0
    · simpa using h0
    · exfalso
      rcases Int.units_eq_one_or (Set.powersetCard.permOfDisjoint hdisj).sign with hs | hs <;>
        rw [hs] at h0 <;> simp at h0 <;> exact htop _ h0
  · intro I _ hI
    rw [mul_smul_comm, ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint, smul_zero, map_zero]
    intro hd
    apply hI
    have hsub : I.val ⊆ J.val := by
      intro i hi
      by_contra hj
      exact Finset.disjoint_left.1 hd (show i ∈ J.valᶜ from Finset.mem_compl.2 hj) hi
    have hle : J.val.card ≤ I.val.card := by
      rw [show (I.val).card = q from I.prop, show (J.val).card = q from J.prop]
    exact Subtype.ext (Finset.eq_of_subset_of_card_le hsub hle)
  · intro hJ; exact absurd (Finset.mem_univ J) hJ

end GlobalTheory.PD

namespace GlobalTheory.PD

/- English proof (translation)
Introduce `k _ _ F K _ _ _ _ _ _ d x h τ hτ p q hpq`. Use `haveI := h.fin`. Use `haveI := h.sep`. Take `⟨b, hb⟩` from `h.exists_basis`. Use `haveI : Module.Finite K Ω[K⁄k] := Module.Finite.of_basis b`.

Use `haveI : Module.Free K Ω[K⁄k] := Module.Free.of_basis b`. Establish `hfr : Module.finrank K Ω[K⁄k] = d` using `by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]`. Use `⟨fun y hy hy0 => ?_, ?_, inferInstance⟩` and prove the remaining obligations. Establish `hτb : τ (ExteriorAlgebra.ιMulti K d b) ≠ 0`. Introduce `h0`.

Establish `hv : vol0 k K x = (∏ j : Fin d, (algebraMap F K (x j.succ / x 0))⁻¹) • ExteriorAlgebra.ιMulti K d b`. Rewrite using `[← AlternatingMap.map_smul_univ]`. Simplify using `only [vol0, hb]`. Establish `h1` using `hτ.1`. Rewrite `h1` using `[hv, map_smul, h0, smul_zero]`.

Conclude with `zero_ne_one h1`. Establish `h2 : ∀ a ∈ ⋀[K]^p Ω[K⁄k], τ (a * y) = 0`. Introduce `a ha`. Use `(traceForm_nondegenerate F K).1 _ fun c => ?_` and prove the remaining obligations. Rewrite using `[Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← map_smul, ← smul_mul_assoc]`.

Conclude with `hy0 _ (Submodule.smul_mem _ c ha)`. Substitute `hpq` using the available equality. Conclude with `wedge_pairing_sep b τ hτb y hy h2`. Rewrite using `[exteriorPower.finrank_eq, exteriorPower.finrank_eq, hfr]`. Conclude with `Nat.choose_symm_of_eq_add hpq.symm`.
-/
theorem IsFinCover.trace_wedge_perfect : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ p q : ℕ, p + q = d → (∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ ⋀[K]^p Ω[K⁄k], Algebra.trace F K (τ (a * y)) = 0) → y = 0) ∧ Module.finrank K (⋀[K]^p Ω[K⁄k]) = Module.finrank K (⋀[K]^q Ω[K⁄k]) ∧ FiniteDimensional K (⋀[K]^p Ω[K⁄k]) := by
  intro k _ _ F K _ _ _ _ _ _ d x h τ hτ p q hpq
  haveI := h.fin
  haveI := h.sep
  obtain ⟨b, hb⟩ := h.exists_basis
  haveI : Module.Finite K Ω[K⁄k] := Module.Finite.of_basis b
  haveI : Module.Free K Ω[K⁄k] := Module.Free.of_basis b
  have hfr : Module.finrank K Ω[K⁄k] = d := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  refine ⟨fun y hy hy0 => ?_, ?_, inferInstance⟩
  · have hτb : τ (ExteriorAlgebra.ιMulti K d b) ≠ 0 := by
      intro h0
      have hv : vol0 k K x =
          (∏ j : Fin d, (algebraMap F K (x j.succ / x 0))⁻¹) • ExteriorAlgebra.ιMulti K d b := by
        rw [← AlternatingMap.map_smul_univ]
        simp only [vol0, hb]
      have h1 := hτ.1
      rw [hv, map_smul, h0, smul_zero] at h1
      exact zero_ne_one h1
    have h2 : ∀ a ∈ ⋀[K]^p Ω[K⁄k], τ (a * y) = 0 := by
      intro a ha
      refine (traceForm_nondegenerate F K).1 _ fun c => ?_
      rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← map_smul, ← smul_mul_assoc]
      exact hy0 _ (Submodule.smul_mem _ c ha)
    subst hpq
    exact wedge_pairing_sep b τ hτb y hy h2
  · rw [exteriorPower.finrank_eq, exteriorPower.finrank_eq, hfr]
    exact Nat.choose_symm_of_eq_add hpq.symm

end GlobalTheory.PD
