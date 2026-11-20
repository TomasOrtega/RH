import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
open GlobalTheory.Published
open scoped IntermediateField

noncomputable section

namespace GlobalTheory.EquidistJ

/- English proof (translation)
Set `E` to `IntermediateField.extendScalars hML`. Establish `hEL : Module.finrank ℚ E = Module.finrank ℚ L` using `rfl`. Establish `hEpos : 0 < Module.finrank ℚ E` using `by rw [hEL]; exact Module.finrank_pos`. Use `haveI : FiniteDimensional ℚ E := Module.finite_of_finrank_pos hEpos`. Use `haveI : FiniteDimensional M E := FiniteDimensional.right ℚ M E`.

Set `ι : L →+* E` to `{ toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }`. Set `ι' : E →+* L` to `{ toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }`. Set `e : {τ : L →+* ℂ // ∀ x : L, (x : ℂ) ∈ M → τ x = σ x} ≃ (E →ₐ[M] ℂ)` to `{ toFun := fun τ => { toRingHom := σ.symm.toRingHom.comp (τ.1.comp ι') commutes' := fun m => by`. Express the relevant statement in the definitionally equal form `σ.symm (τ.1 ⟨m.1, hML m.2⟩) = m.1`. Rewrite using `[τ.2 ⟨m.1, hML m.2⟩ m.2]`.

Conclude with `σ.symm_apply_apply _ }`. Use `invFun := fun f => ⟨σ.toRingHom.comp (f.toRingHom.comp ι), fun x hx => by`. Express the relevant statement in the definitionally equal form `σ (f ⟨x.1, x.2⟩) = σ x.1`. Use `congr 1`. Conclude with `f.commutes ⟨x.1, hx⟩⟩`.

Use `left_inv := fun τ => Subtype.ext (RingHom.ext fun x => by`. Express the relevant statement in the definitionally equal form `σ (σ.symm (τ.1 ⟨x.1, x.2⟩)) = τ.1 x`. Rewrite using `[σ.apply_symm_apply])`. Use `right_inv := fun f => AlgHom.ext fun x => by`. Express the relevant statement in the definitionally equal form `σ.symm (σ (f ⟨x.1, x.2⟩)) = f x`.

Rewrite using `[σ.symm_apply_apply] }`. Rewrite using `[Nat.card_congr e, Nat.card_eq_fintype_card, AlgHom.card M E ℂ, mul_comm, Module.finrank_mul_finrank ℚ M E, hEL]`.
-/
theorem card_ext_mul_finrank (L M : IntermediateField ℚ ℂ) (hML : M ≤ L) [FiniteDimensional ℚ L] (σ : ℂ ≃+* ℂ) :
    Nat.card {τ : L →+* ℂ // ∀ x : L, (x : ℂ) ∈ M → τ x = σ x} * Module.finrank ℚ M = Module.finrank ℚ L := by
  let E := IntermediateField.extendScalars hML
  have hEL : Module.finrank ℚ E = Module.finrank ℚ L := rfl
  have hEpos : 0 < Module.finrank ℚ E := by rw [hEL]; exact Module.finrank_pos
  haveI : FiniteDimensional ℚ E := Module.finite_of_finrank_pos hEpos
  haveI : FiniteDimensional M E := FiniteDimensional.right ℚ M E
  let ι : L →+* E :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  let ι' : E →+* L :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  let e : {τ : L →+* ℂ // ∀ x : L, (x : ℂ) ∈ M → τ x = σ x} ≃ (E →ₐ[M] ℂ) :=
    { toFun := fun τ =>
        { toRingHom := σ.symm.toRingHom.comp (τ.1.comp ι')
          commutes' := fun m => by
            change σ.symm (τ.1 ⟨m.1, hML m.2⟩) = m.1
            rw [τ.2 ⟨m.1, hML m.2⟩ m.2]
            exact σ.symm_apply_apply _ }
      invFun := fun f => ⟨σ.toRingHom.comp (f.toRingHom.comp ι), fun x hx => by
          change σ (f ⟨x.1, x.2⟩) = σ x.1
          congr 1
          exact f.commutes ⟨x.1, hx⟩⟩
      left_inv := fun τ => Subtype.ext (RingHom.ext fun x => by
          change σ (σ.symm (τ.1 ⟨x.1, x.2⟩)) = τ.1 x
          rw [σ.apply_symm_apply])
      right_inv := fun f => AlgHom.ext fun x => by
          change σ.symm (σ (f ⟨x.1, x.2⟩)) = f x
          rw [σ.symm_apply_apply] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, AlgHom.card M E ℂ, mul_comm,
    Module.finrank_mul_finrank ℚ M E, hEL]

/- English proof (translation)
Introduce `hH K _ _ _ h2 φK ΛK hΛ 𝔞 h𝔞`. Use `letI : Algebra K ℂ := φK.toAlgebra`. Establish `hj : ∀ Λ : PeriodPair, jLat Λ = (latticeCurve Λ).j` using `fun Λ => by rw [latticeCurve_j_eq]; rfl`. Establish `hlat : ∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : PeriodPair), IsLatOf φK (𝔟 : FractionalIdeal (𝓞 K)⁰ K) Λ → IsIdealLattice 𝔟 Λ` using `fun _ _ h => h`. Take `⟨-, hfin, hcl, -, hrange⟩` from `hH K h2 ΛK (hlat 1 ΛK hΛ)`.

Use `set H : IntermediateField K ℂ := K⟮(latticeCurve ΛK).j⟯ with hHdef`. Establish `hpos : 0 < Module.finrank K H` using `hfin ▸ Fintype.card_pos`. Use `haveI : FiniteDimensional K H := Module.finite_of_finrank_pos hpos`. Establish `hj0 : (latticeCurve ΛK).j ∈ H` using `IntermediateField.mem_adjoin_simple_self K _`. Establish `hj0' : jLat ΛK ∈ H` using `by rw [hj]; exact hj0`.

Establish `halg : IsAlgebraic ℚ (jLat ΛK)`. Rewrite using `[hj]`. Conclude with `(IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (⟨_, hj0⟩ : H))).restrictScalars ℚ`. Establish `hclass : ∀ σ σ' : ℂ ≃+* ℂ, Fixes φK σ → Fixes φK σ' → (ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') ↔ σ (jLat ΛK) = σ' (jLat ΛK))`. Introduce `σ σ' hσ hσ'`.

Take `⟨Λ, hl, hjl⟩` from `h𝔞 σ hσ`. Take `⟨Λ', hl', hjl'⟩` from `h𝔞 σ' hσ'`. Rewrite using `[← hjl, ← hjl', hj, hj]`. Conclude with `(hcl _ _ Λ Λ' (hlat _ _ hl) (hlat _ _ hl')).symm`. Use `⟨halg, hclass, ?_⟩` and prove the remaining obligations.

Introduce `L hLf hLg hKL hjL C`. Take `⟨I, rfl⟩` from `ClassGroup.mk0_surjective C`. Take `⟨Lb, hLb⟩` from `exists_isIdealLattice h2 (FractionalIdeal.mk0 K I)`. Establish `hinv : (latticeCurve Lb).j ∈ idealInvariants K` using `⟨_, Lb, hLb, rfl⟩`. Rewrite `hinv` using `[← hrange]`.

Take `⟨g, hg⟩` from `hinv`. Use `haveI : NumberField H := NumberField.of_module_finite K H`. Use `haveI : Countable H := (Module.finBasis ℚ H).equivFun.injective.countable`. Take `⟨σC, hσC⟩` from `GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq H.val.toRingHom (H.val.toRingHom.comp g.toAlgHom.toRingHom)`. Establish `hfixC : Fixes φK σC` using `fun x => by`.

Use `hσC (algebraMap K H x)` as an intermediate fact. Conclude with `(by simpa using this : σC (algebraMap K ℂ x) = algebraMap K ℂ x)`. Establish `hσCj : σC (jLat ΛK) = jLat Lb`. Use `hσC (IntermediateField.AdjoinSimple.gen K (latticeCurve ΛK).j)` as an intermediate fact. Rewrite using `[hj, hj]`.

Simplify `this` using `[hg]`. Establish `hclC : ClassGroup.mk K (𝔞 σC) = ClassGroup.mk0 I`. Take `⟨Λ, hl, hjl⟩` from `h𝔞 σC hfixC`. Rewrite using `[← ClassGroup.mk_mk0 K]`. Use `(hcl _ _ Λ Lb (hlat _ _ hl) hLb).1 ?_` and prove the remaining obligations.

Rewrite using `[← hj, hjl, hσCj, hj]`. Set `L' : IntermediateField K ℂ` to `L.toSubfield.toIntermediateField hKL`. Establish `hHL : H ≤ L'` using `IntermediateField.adjoin_simple_le_iff.2 (by rw [← hj]; exact hjL)`. Use `haveI : FiniteDimensional ℚ L := hLf`. Use `haveI : Countable L := (Module.finBasis ℚ L).equivFun.injective.countable`.

Establish `hcount` using `card_ext_mul_finrank L (H.restrictScalars ℚ) (fun x hx => hHL hx) σC`. Establish `hM : Module.finrank ℚ (H.restrictScalars ℚ) = Module.finrank ℚ K * Module.finrank K H`. Rewrite using `[Module.finrank_mul_finrank ℚ K H]`. Both sides reduce to the same expression. Rewrite `hcount` using `[hM, h2, hfin]`.

Establish `hiff : ∀ τ : L →+* ℂ, (∃ σ : ℂ ≃+* ℂ, Fixes φK σ ∧ (∀ x : L, σ (x : ℂ) = τ x) ∧ ClassGroup.mk K (𝔞 σ) = ClassGroup.mk0 I) ↔ ∀ x : L, (x : ℂ) ∈ H.restrictScalars ℚ → τ x = σC x`. Introduce `τ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨σ, hσ, hστ, hcσ⟩ x hx`. Establish `e : σ (jLat ΛK) = σC (jLat ΛK)` using `(hclass σ σC hσ hfixC).1 (hcσ.trans hclC.symm)`.

Rewrite `e` using `[hj]`. Set `a : H →ₐ[K] ℂ` to `((AlgEquiv.ofRingEquiv (f := σ) hσ).toAlgHom).comp H.val`. Set `b : H →ₐ[K] ℂ` to `((AlgEquiv.ofRingEquiv (f := σC) hfixC).toAlgHom).comp H.val`. Establish `hab : a = b`. Use `IntermediateField.algHom_ext_of_eq_adjoin K rfl ?_` and prove the remaining obligations.

Introduce and unpack `y rfl`. Conclude with `e`. Rewrite using `[← hστ x]`. Conclude with `DFunLike.congr_fun hab ⟨x, hx⟩`. Introduce `hτ`.

Take `⟨σ, hσ⟩` from `GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq L.val.toRingHom τ`. Establish `hσf : Fixes φK σ` using `fun x => by`. Establish `h1` using `hσ ⟨φK x, hKL x⟩`. Establish `h2` using `hτ ⟨φK x, hKL x⟩ (H.algebraMap_mem x)`. Establish `h3` using `hfixC x`.

Conclude with `h1.trans (h2.trans h3)`. Use `⟨σ, hσf, fun x => hσ x, ?_⟩` and prove the remaining obligations. Use `((hclass σ σC hσf hfixC).2 ?_).trans hclC` and prove the remaining obligations. Establish `h1` using `hσ ⟨jLat ΛK, hjL⟩`. Establish `h2` using `hτ ⟨jLat ΛK, hjL⟩ hj0'`.

Conclude with `h1.trans h2`. Rewrite using `[Nat.card_congr (Equiv.subtypeEquivRight hiff)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem equidistributed_of_hilbertClassFieldJ : ∀ (hH : GlobalTheory.Published.HilbertClassFieldJ) {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair) (hΛ : IsLatOf φK 1 ΛK) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔞 : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ Λ : PeriodPair, IsLatOf φK (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) Λ ∧ jLat Λ = σ (jLat ΛK)), Equidistributed φK (jLat ΛK) 𝔞 := by
  intro hH K _ _ _ h2 φK ΛK hΛ 𝔞 h𝔞
  letI : Algebra K ℂ := φK.toAlgebra
  have hj : ∀ Λ : PeriodPair, jLat Λ = (latticeCurve Λ).j := fun Λ => by rw [latticeCurve_j_eq]; rfl
  have hlat : ∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : PeriodPair),
      IsLatOf φK (𝔟 : FractionalIdeal (𝓞 K)⁰ K) Λ → IsIdealLattice 𝔟 Λ := fun _ _ h => h
  obtain ⟨-, hfin, hcl, -, hrange⟩ := hH K h2 ΛK (hlat 1 ΛK hΛ)
  set H : IntermediateField K ℂ := K⟮(latticeCurve ΛK).j⟯ with hHdef
  have hpos : 0 < Module.finrank K H := hfin ▸ Fintype.card_pos
  haveI : FiniteDimensional K H := Module.finite_of_finrank_pos hpos
  have hj0 : (latticeCurve ΛK).j ∈ H := IntermediateField.mem_adjoin_simple_self K _
  have hj0' : jLat ΛK ∈ H := by rw [hj]; exact hj0
  have halg : IsAlgebraic ℚ (jLat ΛK) := by
    rw [hj]
    exact (IntermediateField.isAlgebraic_iff.1
      (Algebra.IsAlgebraic.isAlgebraic (⟨_, hj0⟩ : H))).restrictScalars ℚ
  have hclass : ∀ σ σ' : ℂ ≃+* ℂ, Fixes φK σ → Fixes φK σ' →
      (ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') ↔ σ (jLat ΛK) = σ' (jLat ΛK)) := by
    intro σ σ' hσ hσ'
    obtain ⟨Λ, hl, hjl⟩ := h𝔞 σ hσ
    obtain ⟨Λ', hl', hjl'⟩ := h𝔞 σ' hσ'
    rw [← hjl, ← hjl', hj, hj]
    exact (hcl _ _ Λ Λ' (hlat _ _ hl) (hlat _ _ hl')).symm
  refine ⟨halg, hclass, ?_⟩
  intro L hLf hLg hKL hjL C
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective C
  obtain ⟨Lb, hLb⟩ := exists_isIdealLattice h2 (FractionalIdeal.mk0 K I)
  have hinv : (latticeCurve Lb).j ∈ idealInvariants K := ⟨_, Lb, hLb, rfl⟩
  rw [← hrange] at hinv
  obtain ⟨g, hg⟩ := hinv
  haveI : NumberField H := NumberField.of_module_finite K H
  haveI : Countable H := (Module.finBasis ℚ H).equivFun.injective.countable
  obtain ⟨σC, hσC⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq H.val.toRingHom
    (H.val.toRingHom.comp g.toAlgHom.toRingHom)
  have hfixC : Fixes φK σC := fun x => by
    have := hσC (algebraMap K H x)
    exact (by simpa using this : σC (algebraMap K ℂ x) = algebraMap K ℂ x)
  have hσCj : σC (jLat ΛK) = jLat Lb := by
    have := hσC (IntermediateField.AdjoinSimple.gen K (latticeCurve ΛK).j)
    rw [hj, hj]
    simpa [hg] using this
  have hclC : ClassGroup.mk K (𝔞 σC) = ClassGroup.mk0 I := by
    obtain ⟨Λ, hl, hjl⟩ := h𝔞 σC hfixC
    rw [← ClassGroup.mk_mk0 K]
    refine (hcl _ _ Λ Lb (hlat _ _ hl) hLb).1 ?_
    rw [← hj, hjl, hσCj, hj]
  let L' : IntermediateField K ℂ := L.toSubfield.toIntermediateField hKL
  have hHL : H ≤ L' := IntermediateField.adjoin_simple_le_iff.2 (by rw [← hj]; exact hjL)
  haveI : FiniteDimensional ℚ L := hLf
  haveI : Countable L := (Module.finBasis ℚ L).equivFun.injective.countable
  have hcount := card_ext_mul_finrank L (H.restrictScalars ℚ) (fun x hx => hHL hx) σC
  have hM : Module.finrank ℚ (H.restrictScalars ℚ) = Module.finrank ℚ K * Module.finrank K H := by
    rw [Module.finrank_mul_finrank ℚ K H]
    rfl
  rw [hM, h2, hfin] at hcount
  have hiff : ∀ τ : L →+* ℂ, (∃ σ : ℂ ≃+* ℂ, Fixes φK σ ∧ (∀ x : L, σ (x : ℂ) = τ x) ∧
      ClassGroup.mk K (𝔞 σ) = ClassGroup.mk0 I) ↔ ∀ x : L, (x : ℂ) ∈ H.restrictScalars ℚ → τ x = σC x := by
    intro τ
    constructor
    · rintro ⟨σ, hσ, hστ, hcσ⟩ x hx
      have e : σ (jLat ΛK) = σC (jLat ΛK) := (hclass σ σC hσ hfixC).1 (hcσ.trans hclC.symm)
      rw [hj] at e
      let a : H →ₐ[K] ℂ := ((AlgEquiv.ofRingEquiv (f := σ) hσ).toAlgHom).comp H.val
      let b : H →ₐ[K] ℂ := ((AlgEquiv.ofRingEquiv (f := σC) hfixC).toAlgHom).comp H.val
      have hab : a = b := by
        refine IntermediateField.algHom_ext_of_eq_adjoin K rfl ?_
        rintro y rfl
        exact e
      rw [← hστ x]
      exact DFunLike.congr_fun hab ⟨x, hx⟩
    · intro hτ
      obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq L.val.toRingHom τ
      have hσf : Fixes φK σ := fun x => by
        have h1 := hσ ⟨φK x, hKL x⟩
        have h2 := hτ ⟨φK x, hKL x⟩ (H.algebraMap_mem x)
        have h3 := hfixC x
        exact h1.trans (h2.trans h3)
      refine ⟨σ, hσf, fun x => hσ x, ?_⟩
      refine ((hclass σ σC hσf hfixC).2 ?_).trans hclC
      have h1 := hσ ⟨jLat ΛK, hjL⟩
      have h2 := hτ ⟨jLat ΛK, hjL⟩ hj0'
      exact h1.trans h2
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  linarith

end GlobalTheory.EquidistJ
