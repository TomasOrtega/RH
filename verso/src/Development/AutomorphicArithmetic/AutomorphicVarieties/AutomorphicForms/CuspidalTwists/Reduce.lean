import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero

noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.Mem.Chr.CharModel

namespace UpperTheory.V.TR.SS

/- English proof (translation)
Set `A` to `Algebra.adjoin ℂ (Set.range act)`. Set `up : ∀ U : Submodule ℂ M, (∀ o, ∀ x ∈ U, act o x ∈ U) → Submodule A M` to `fun U hU => { U.toAddSubmonoid with smul_mem' := by`. Introduce and unpack `⟨z, hz⟩ x hx`. Express the relevant statement in the definitionally equal form `z x ∈ U`. Proceed by induction on `hz using Algebra.adjoin_induction generalizing x with`.

Consider the case `mem z hz => obtain ⟨o, rfl⟩ := hz`. Conclude with `hU o x hx`. Consider the case `algebraMap c => exact U.smul_mem c hx`. Consider the case `add y z _ _ h1 h2 => exact U.add_mem (h1 hx) (h2 hx)`. Consider the case `mul y z _ _ h1 h2 => exact h1 (h2 hx) }`.

Establish `hdown : ∀ N : Submodule A M, ∀ o, ∀ x ∈ N.restrictScalars ℂ, act o x ∈ N.restrictScalars ℂ` using `fun N o x hx => N.smul_mem (⟨act o, Algebra.subset_adjoin ⟨o, rfl⟩⟩ : A) hx`. Establish `hud : ∀ U hU, (up U hU).restrictScalars ℂ = U` using `fun U hU => rfl`. Set `C'` to `up C hC`. Establish `hI : ComplementedLattice (Set.Iic C')` using `⟨fun N => by`. Take `⟨D, h1, h2, h3, h4⟩` from `hc (N.1.restrictScalars ℂ) N.2 (hdown _)`.

Use `⟨⟨up D h2, h1⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[disjoint_iff]`. Use `Subtype.ext (Submodule.restrictScalars_injective ℂ _ _ ?_)` and prove the remaining obligations. Conclude with `h3`. Rewrite using `[codisjoint_iff]`.

Use `Subtype.ext (Submodule.restrictScalars_injective ℂ _ _ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(N.1 ⊔ up D h2).restrictScalars ℂ = C`. Rewrite using `[Submodule.restrictScalars_sup]`. Conclude with `h4⟩`. Establish `hL : ComplementedLattice (Submodule A C')` using `(Submodule.mapIic C').complementedLattice_iff.2 hI`.

Establish `hat : IsAtomistic (Submodule A C')` using `isAtomistic_of_complementedLattice`. Introduce `x hx`. Establish `hx' : (⟨x, hx⟩ : C') ∈ sSup {a : Submodule A C' | IsAtom a}`. Rewrite using `[sSup_atoms_eq_top]`. Discharge the goal by the elementary cases of `trivial`.

Rewrite `hx'` using `[sSup_eq_iSup']`. Generalize the expression as in `hS : sSup {V : Submodule ℂ M | V ≤ C ∧ (∀ o, ∀ x ∈ V, act o x ∈ V) ∧ V ≠ ⊥ ∧ ∀ W ≤ V, (∀ o, ∀ x ∈ W, act o x ∈ W) → W = ⊥ ∨ W = V} = S`. Use `Submodule.iSup_induction _ (motive := fun y : C' => y.1 ∈ S) hx' ?_ S.zero_mem fun _ _ => S.add_mem` and prove the remaining obligations. Introduce and unpack `⟨N, hN⟩ y hy`. Establish `hN' : IsAtom (N.map C'.subtype)` using `(((Submodule.mapIic C').isAtom_iff N).2 hN).of_isAtom_coe_Iic`.

Establish `hle : (N.map C'.subtype).restrictScalars ℂ ≤ S`. Rewrite using `[← hS]`. Use `le_sSup ⟨C'.map_subtype_le N, hdown _, fun h => hN'.1 (Submodule.restrictScalars_injective ℂ _ _ h), fun W hW hs => ?_⟩` and prove the remaining obligations. Conclude with `(hN'.le_iff.1 (show up W hs ≤ _ from hW)).imp (congrArg (Submodule.restrictScalars ℂ)) (congrArg (Submodule.restrictScalars ℂ))`. Conclude with `hle ⟨y, hy, rfl⟩`.
-/
theorem le_sSup_minimal {M O : Type*} [AddCommGroup M] [Module ℂ M] (act : O → Module.End ℂ M) (C : Submodule ℂ M)
    (hC : ∀ o, ∀ x ∈ C, act o x ∈ C)
    (hc : ∀ U ≤ C, (∀ o, ∀ x ∈ U, act o x ∈ U) →
      ∃ D ≤ C, (∀ o, ∀ x ∈ D, act o x ∈ D) ∧ U ⊓ D = ⊥ ∧ U ⊔ D = C) :
    C ≤ sSup {V | V ≤ C ∧ (∀ o, ∀ x ∈ V, act o x ∈ V) ∧ V ≠ ⊥ ∧
      ∀ W ≤ V, (∀ o, ∀ x ∈ W, act o x ∈ W) → W = ⊥ ∨ W = V} := by
  let A := Algebra.adjoin ℂ (Set.range act)
  let up : ∀ U : Submodule ℂ M, (∀ o, ∀ x ∈ U, act o x ∈ U) → Submodule A M := fun U hU =>
    { U.toAddSubmonoid with
      smul_mem' := by
        rintro ⟨z, hz⟩ x hx
        change z x ∈ U
        induction hz using Algebra.adjoin_induction generalizing x with
        | mem z hz => obtain ⟨o, rfl⟩ := hz; exact hU o x hx
        | algebraMap c => exact U.smul_mem c hx
        | add y z _ _ h1 h2 => exact U.add_mem (h1 hx) (h2 hx)
        | mul y z _ _ h1 h2 => exact h1 (h2 hx) }
  have hdown : ∀ N : Submodule A M, ∀ o, ∀ x ∈ N.restrictScalars ℂ, act o x ∈ N.restrictScalars ℂ := fun N o x hx =>
    N.smul_mem (⟨act o, Algebra.subset_adjoin ⟨o, rfl⟩⟩ : A) hx
  have hud : ∀ U hU, (up U hU).restrictScalars ℂ = U := fun U hU => rfl
  let C' := up C hC
  have hI : ComplementedLattice (Set.Iic C') := ⟨fun N => by
    obtain ⟨D, h1, h2, h3, h4⟩ := hc (N.1.restrictScalars ℂ) N.2 (hdown _)
    refine ⟨⟨up D h2, h1⟩, ?_, ?_⟩
    · rw [disjoint_iff]
      refine Subtype.ext (Submodule.restrictScalars_injective ℂ _ _ ?_)
      exact h3
    · rw [codisjoint_iff]
      refine Subtype.ext (Submodule.restrictScalars_injective ℂ _ _ ?_)
      change (N.1 ⊔ up D h2).restrictScalars ℂ = C
      rw [Submodule.restrictScalars_sup]
      exact h4⟩
  have hL : ComplementedLattice (Submodule A C') := (Submodule.mapIic C').complementedLattice_iff.2 hI
  have hat : IsAtomistic (Submodule A C') := isAtomistic_of_complementedLattice
  intro x hx
  have hx' : (⟨x, hx⟩ : C') ∈ sSup {a : Submodule A C' | IsAtom a} := by
    rw [sSup_atoms_eq_top]; trivial
  rw [sSup_eq_iSup'] at hx'
  generalize hS : sSup {V : Submodule ℂ M | V ≤ C ∧ (∀ o, ∀ x ∈ V, act o x ∈ V) ∧ V ≠ ⊥ ∧
      ∀ W ≤ V, (∀ o, ∀ x ∈ W, act o x ∈ W) → W = ⊥ ∨ W = V} = S
  refine Submodule.iSup_induction _ (motive := fun y : C' => y.1 ∈ S) hx' ?_ S.zero_mem fun _ _ => S.add_mem
  rintro ⟨N, hN⟩ y hy
  have hN' : IsAtom (N.map C'.subtype) := (((Submodule.mapIic C').isAtom_iff N).2 hN).of_isAtom_coe_Iic
  have hle : (N.map C'.subtype).restrictScalars ℂ ≤ S := by
    rw [← hS]
    refine le_sSup ⟨C'.map_subtype_le N, hdown _, fun h => hN'.1 (Submodule.restrictScalars_injective ℂ _ _ h), fun W hW hs => ?_⟩
    exact (hN'.le_iff.1 (show up W hs ≤ _ from hW)).imp (congrArg (Submodule.restrictScalars ℂ)) (congrArg (Submodule.restrictScalars ℂ))
  exact hle ⟨y, hy, rfl⟩

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

/- English proof (translation)
Use `expo_eq_of_exp _ v s fun t => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Complex.exp (s * logNorm F (infId F (expU (Pi.single v t)))) = _`. Establish `h1 : finPart F (infId F (expU (Pi.single v t))) = 1` using `Units.ext (by`. Express the relevant statement in the definitionally equal form `(1 : Af F) - 0 + 0 = 1`. Use the proof step `simp)`.

Establish `h2 : ∀ u, ‖(infPart F (infId F (expU (Pi.single v t)))).val u‖ = Real.exp ((Pi.single v t : Rinf F) u)` using `fun u => by`. Establish `e : (infPart F (infId F (expU (Pi.single v t)))).val = infEq F (expU (Pi.single v t)).val`. Express the relevant statement in the definitionally equal form `1 - infEq F 1 + infEq F _ = _`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Conclude with `(((InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal u)).symm.isometry.norm_map_of_map_zero (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm)) _).trans (Real.norm_of_nonneg (Real.exp_pos _).le)`. Rewrite using `[logNorm, h1, logFin_one, logInf]`. Simplify using `[h2, Pi.single_apply, InfinitePlace.mult, IsTotallyReal.isReal]`.
-/
theorem expo_absC (s : ℂ) (v : InfinitePlace F) : expo (GlobalTheory.CuspRep.Model.absC F s) v = s := by
  classical
  refine expo_eq_of_exp _ v s fun t => ?_
  change Complex.exp (s * logNorm F (infId F (expU (Pi.single v t)))) = _
  have h1 : finPart F (infId F (expU (Pi.single v t))) = 1 := Units.ext (by
    change (1 : Af F) - 0 + 0 = 1
    simp)
  have h2 : ∀ u, ‖(infPart F (infId F (expU (Pi.single v t)))).val u‖ = Real.exp ((Pi.single v t : Rinf F) u) := fun u => by
    have e : (infPart F (infId F (expU (Pi.single v t)))).val = infEq F (expU (Pi.single v t)).val := by
      change 1 - infEq F 1 + infEq F _ = _
      simp
    rw [e]
    exact (((InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal u)).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm)) _).trans
      (Real.norm_of_nonneg (Real.exp_pos _).le)
  rw [logNorm, h1, logFin_one, logInf]
  simp [h2, Pi.single_apply, InfinitePlace.mult, IsTotallyReal.isReal]

/- English proof (translation)
Establish `hn : (Fintype.card (InfinitePlace F) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Establish `ha' : (a : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 ha`. Use `⟨GlobalTheory.CuspRep.Model.absC F (-s / (Fintype.card (InfinitePlace F) * a)), ?_⟩` and prove the remaining obligations. Establish `ht : (Matrix.of (oneL F a)).trace = (a : Rinf F)`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin a) (Fin a) (Rinf F)).trace = _`.

Simplify using the standard rewrite rules. Rewrite using `[lie_mulChi, h, ← add_smul, dchi_eq_sum, ht]`. Simplify using `only [expo_absC, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Pi.natCast_apply, Complex.ofReal_natCast]`. Establish `: s + (Fintype.card (InfinitePlace F) : ℂ) * (-s / (Fintype.card (InfinitePlace F) * a) * a) = 0` using `by field_simp; ring`. Rewrite using `[this, zero_smul, map_zero]`.
-/
theorem exists_twist_zero (ha : a ≠ 0) {φ : Sm F a} {s : ℂ} (h : lie F a (oneL F a) φ = s • φ) :
    ∃ χ : HChar F, lie F a (oneL F a) (mulChi a χ φ) = 0 := by
  have hn : (Fintype.card (InfinitePlace F) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha
  refine ⟨GlobalTheory.CuspRep.Model.absC F (-s / (Fintype.card (InfinitePlace F) * a)), ?_⟩
  have ht : (Matrix.of (oneL F a)).trace = (a : Rinf F) := by
    change (1 : Matrix (Fin a) (Fin a) (Rinf F)).trace = _
    simp
  rw [lie_mulChi, h, ← add_smul, dchi_eq_sum, ht]
  simp only [expo_absC, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Pi.natCast_apply, Complex.ofReal_natCast]
  have : s + (Fintype.card (InfinitePlace F) : ℂ) * (-s / (Fintype.card (InfinitePlace F) * a) * a) = 0 := by
    field_simp; ring
  rw [this, zero_smul, map_zero]

variable (F a) in

def ZeroCompl : Prop :=
  ∃ C : Submodule ℂ (Sm F a), (∀ φ ∈ C, IsCuspForm φ) ∧ (∀ φ, IsCuspForm φ → lie F a (oneL F a) φ = 0 → φ ∈ C) ∧ IsStable C ∧
    ∀ U ≤ C, IsStable U → ∃ D ≤ C, IsStable D ∧ U ⊓ D = ⊥ ∧ U ⊔ D = C

/- English proof (translation)
Take `⟨C, hm, hm', hs, hc⟩` from `h`. Use `(le_sSup_minimal act C hs hc).trans (sSup_le ?_) (hm' φ h1 h2)` and prove the remaining obligations. Introduce and unpack `V ⟨h3, h4, h5, h6⟩`. Conclude with `le_iSup (fun π : CuspSub F a => π.V) ⟨V, fun ψ hψ => hm ψ (h3 hψ), h4, h5, h6⟩`.
-/
theorem mem_iSup_of_zero (h : ZeroCompl F a) {φ : Sm F a} (h1 : IsCuspForm φ) (h2 : lie F a (oneL F a) φ = 0) :
    φ ∈ ⨆ π : CuspSub F a, π.V := by
  obtain ⟨C, hm, hm', hs, hc⟩ := h
  refine (le_sSup_minimal act C hs hc).trans (sSup_le ?_) (hm' φ h1 h2)
  rintro V ⟨h3, h4, h5, h6⟩
  exact le_iSup (fun π : CuspSub F a => π.V) ⟨V, fun ψ hψ => hm ψ (h3 hψ), h4, h5, h6⟩

/- English proof (translation)
Establish `: (⨆ π : CuspSub F a, π.V).map (mulChi a χ).toLinearMap ≤ ⨆ π : CuspSub F a, π.V`. Rewrite using `[Submodule.map_iSup]`. Conclude with `iSup_le fun π => le_iSup (fun π : CuspSub F a => π.V) (π.twist χ)`. Conclude with `this ⟨φ, h, rfl⟩`.
-/
theorem mulChi_mem_iSup (χ : HChar F) {φ : Sm F a} (h : φ ∈ ⨆ π : CuspSub F a, π.V) :
    mulChi a χ φ ∈ ⨆ π : CuspSub F a, π.V := by
  have : (⨆ π : CuspSub F a, π.V).map (mulChi a χ).toLinearMap ≤ ⨆ π : CuspSub F a, π.V := by
    rw [Submodule.map_iSup]
    exact iSup_le fun π => le_iSup (fun π : CuspSub F a => π.V) (π.twist χ)
  exact this ⟨φ, h, rfl⟩

/- English proof (translation)
Introduce and unpack `F _ _ _ a φ hφ ⟨s, hs⟩`. Break down `eq_or_ne a 0 with rfl | ha` into its components or cases. Use `le_iSup (fun π : CuspSub F 0 => π.V) (CuspSub.triv F zero_le_one) ?_` and prove the remaining obligations. Conclude with `Submodule.mem_span_singleton.2 ⟨φ.1 1, Subtype.ext (funext fun g => by`. Rewrite using `[Subsingleton.elim g 1]`.

Conclude with `mul_one _)⟩`. Take `⟨χ, hχ⟩` from `exists_twist_zero ha hs`. Establish `h1` using `mulChi_mem_iSup χ⁻¹ (mem_iSup_of_zero (h F a) (hφ.mulChi χ) hχ)`. Rewrite `h1` using `[← mulChi_mul, mul_inv_cancel, mulChi_one]`. Then use the resulting hypothesis.
-/
theorem cuspSemisimple_of (h : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), ZeroCompl F a) :
    UpperTheory.V.Published.CuspSemisimpleReal := by
  rintro F _ _ _ a φ hφ ⟨s, hs⟩
  rcases eq_or_ne a 0 with rfl | ha
  · refine le_iSup (fun π : CuspSub F 0 => π.V) (CuspSub.triv F zero_le_one) ?_
    exact Submodule.mem_span_singleton.2 ⟨φ.1 1, Subtype.ext (funext fun g => by
      rw [Subsingleton.elim g 1]; exact mul_one _)⟩
  · obtain ⟨χ, hχ⟩ := exists_twist_zero ha hs
    have h1 := mulChi_mem_iSup χ⁻¹ (mem_iSup_of_zero (h F a) (hφ.mulChi χ) hχ)
    rwa [← mulChi_mul, mul_inv_cancel, mulChi_one] at h1

end UpperTheory.V.TR.SS
