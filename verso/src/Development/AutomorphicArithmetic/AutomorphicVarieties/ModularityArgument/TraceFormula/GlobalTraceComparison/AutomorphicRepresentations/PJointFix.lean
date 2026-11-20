import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UnitHecke

noncomputable section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open GlobalTheory.CuspRep.LocEx
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.G8

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Simplify using `only [CuspSub.locRep, MonoidHom.comp_apply]`. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, LocUniq.comm_locGL w hc]`.
-/
private theorem fin_comm_loc (π : CuspSub E n) (w : Pl E) {c : GL (Fin n) (Af E)}
    (hc : GeneralLinearGroup.map (pLoc E w) c = 1) (g : GLw n w) (y : π.V) :
    π.finPart c (π.locRep w g y) = π.locRep w g (π.finPart c y) := by
  simp only [CuspSub.locRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, LocUniq.comm_locGL w hc]

/- English proof (translation)
Establish `inj` using `Submodule.map_injective_of_injective π.V.injective_subtype`. Establish `stable : ∀ o, ∀ x ∈ nullPart (π.locRep w) K, π.op o x ∈ nullPart (π.locRep w) K`. Introduce `o x hx`. Consider the cases of `o with`. Consider the case `fin k`.

Establish `e` using `map_pLoc_inv_mul w k`. Establish `h1` using `nullPart_act (π.locRep w) K (GeneralLinearGroup.map (pLoc E w) k) (nullPart_comm (π.locRep w) K (π.finPart ((locGL E n w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g y => fin_comm_loc π w e g y) hx)`. Rewrite `h1` using `[CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`. Then use the resulting hypothesis. Consider the case `cpt k`. Use `nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(rt E n (infGL E n (Unitary.toUnits k)) * rt E n (finGL E n (locGL E n w g))) y.1 = (rt E n (finGL E n (locGL E n w g)) * rt E n (infGL E n (Unitary.toUnits k))) y.1`. Rewrite using `[← map_mul, ← map_mul, infGL_comm]`. Consider the case `lie X`. Conclude with `nullPart_comm _ K _ (fun g y => Subtype.ext (LinearMap.congr_fun (lie_rt_fin X (locGL E n w g)) y.1)) hx`. Use `(π.irred ((nullPart (π.locRep w) K).map π.V.subtype) (Submodule.map_subtype_le _ _) ?_).imp (fun e => inj (e.trans (Submodule.map_bot _).symm)) fun e => inj (e.trans (Submodule.map_subtype_top _).symm)` and prove the remaining obligations.

Introduce and unpack `o _ ⟨x, hx, rfl⟩`. Conclude with `⟨_, stable o x hx, rfl⟩`.
-/
private theorem null_cases (π : CuspSub E n) (w : Pl E) (K : Subgroup (GLw n w)) :
    nullPart (π.locRep w) K = ⊥ ∨ nullPart (π.locRep w) K = ⊤ := by
  have inj := Submodule.map_injective_of_injective π.V.injective_subtype
  have stable : ∀ o, ∀ x ∈ nullPart (π.locRep w) K, π.op o x ∈ nullPart (π.locRep w) K := by
    intro o x hx
    cases o with
    | fin k =>
      have e := map_pLoc_inv_mul w k
      have h1 := nullPart_act (π.locRep w) K (GeneralLinearGroup.map (pLoc E w) k)
        (nullPart_comm (π.locRep w) K (π.finPart ((locGL E n w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k))
          (fun g y => fin_comm_loc π w e g y) hx)
      rwa [CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h1
    | cpt k =>
      refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
      change (rt E n (infGL E n (Unitary.toUnits k)) * rt E n (finGL E n (locGL E n w g))) y.1 =
        (rt E n (finGL E n (locGL E n w g)) * rt E n (infGL E n (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X =>
      exact nullPart_comm _ K _ (fun g y => Subtype.ext (LinearMap.congr_fun (lie_rt_fin X (locGL E n w g)) y.1)) hx
  refine (π.irred ((nullPart (π.locRep w) K).map π.V.subtype) (Submodule.map_subtype_le _ _) ?_).imp
    (fun e => inj (e.trans (Submodule.map_bot _).symm)) fun e => inj (e.trans (Submodule.map_subtype_top _).symm)
  rintro o _ ⟨x, hx, rfl⟩
  exact ⟨_, stable o x hx, rfl⟩

/- English proof (translation)
Assume the negation of the conclusion as `hno`. Establish `hsm : IsSmooth (π.locRep w)` using `fun v => (π.isSmooth_finPart v).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)`. Establish `hc : IsCompact (KGL w n : Set (GLw n w))` using `(Asm.unitHecke E n 0 0 w).2.2.2.1`. Establish `hbot : fixed π.finPart U ⊓ fixed (π.locRep w) (KGL w n) = ⊥`. Use `(Submodule.eq_bot_iff _).2 fun y hy => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hy0`. Conclude with `hno ⟨y, hy0, hy.1, hy.2⟩`. Establish `hst : ∀ g, ∀ v ∈ fixed π.finPart U, π.locRep w g v ∈ fixed π.finPart U` using `fun g v hv => mem_fix.2 fun k hk => by rw [fin_comm_loc π w (hU k hk), mem_fix.1 hv k hk]`. Establish `hle` using `le_nullPart hsm hc _ hst hbot`. Break down `null_cases π w (KGL w n) with h | h` into its components or cases.

Conclude with `h0 (by simpa [h] using hle hψ)`. Take `⟨x, hx0, hxK, -⟩` from `hB.exists_vec`. Conclude with `hx0 (eq_zero_of_mem_nullPart hsm hc hxK (h ▸ Submodule.mem_top))`.
-/
private theorem step (π : CuspSub E n) (w : Pl E) (B : Multiset ℂˣ) (hB : HasSatGL w (π.locRep w) B)
    (U : Subgroup (GL (Fin n) (Af E))) (hU : ∀ k ∈ U, GeneralLinearGroup.map (pLoc E w) k = 1)
    (ψ : π.V) (h0 : ψ ≠ 0) (hψ : ψ ∈ fixed π.finPart U) :
    ∃ y : π.V, y ≠ 0 ∧ y ∈ fixed π.finPart U ∧ y ∈ fixed (π.locRep w) (KGL w n) := by
  by_contra hno
  have hsm : IsSmooth (π.locRep w) := fun v =>
    (π.isSmooth_finPart v).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)
  have hc : IsCompact (KGL w n : Set (GLw n w)) := (Asm.unitHecke E n 0 0 w).2.2.2.1
  have hbot : fixed π.finPart U ⊓ fixed (π.locRep w) (KGL w n) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun y hy => ?_
    by_contra hy0
    exact hno ⟨y, hy0, hy.1, hy.2⟩
  have hst : ∀ g, ∀ v ∈ fixed π.finPart U, π.locRep w g v ∈ fixed π.finPart U := fun g v hv =>
    mem_fix.2 fun k hk => by rw [fin_comm_loc π w (hU k hk), mem_fix.1 hv k hk]
  have hle := le_nullPart hsm hc _ hst hbot
  rcases null_cases π w (KGL w n) with h | h
  · exact h0 (by simpa [h] using hle hψ)
  · obtain ⟨x, hx0, hxK, -⟩ := hB.exists_vec
    exact hx0 (eq_zero_of_mem_nullPart hsm hc hxK (h ▸ Submodule.mem_top))

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem finPart_val (π : CuspSub E n) (g : GL (Fin n) (Af E)) (y : π.V) :
    (π.finPart g y : Sm E n) = finRep E n g y.1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem locRep_val (π : CuspSub E n) (w : Pl E) (a : GLw n w) (y : π.V) :
    (π.locRep w a y : Sm E n) = finRep E n (locGL E n w a) y.1 := rfl

private def fixer (y : Sm E n) : Subgroup (GL (Fin n) (Af E)) where
  carrier := {g | finRep E n g y = y}
  mul_mem' := fun {a b} ha hb => by
    rw [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    rw [Set.mem_setOf_eq] at ha ⊢
    have h : finRep E n a⁻¹ (finRep E n a y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [ha] at h

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `_ E _ _ _ n π P`. Proceed by induction on `P using Finset.induction_on with`. Consider the case `empty`. Introduce and unpack `- U - ⟨ψ, h1, h2, h3⟩`. Conclude with `⟨ψ, h1, h2, h3, by simp⟩`.

Consider the case `insert w P hw ih`. Introduce and unpack `hsat U hU ⟨ψ, hψ, h0, hfix⟩`. Take `⟨B, hB⟩` from `hsat w (Finset.mem_insert_self _ _)`. Take `⟨y, hy0, hyU, hyK⟩` from `step π w B hB U (fun k hk => hU k hk w (Finset.mem_insert_self _ _)) ⟨ψ, hψ⟩ (fun e => h0 (congrArg Subtype.val e)) (mem_fix.2 fun k hk => Subtype.ext ((finPart_val π k ⟨ψ, hψ⟩).trans (hfix k hk)))`. Establish `hU' : ∀ k ∈ U ⊔ (KGL w n).map (locGL E n w), ∀ v ∈ P, qw n v false k = 1`.

Introduce `k hk v hv`. Establish `hvw : v ≠ w` using `fun e => hw (e ▸ hv)`. Establish `hle : U ⊔ (KGL w n).map (locGL E n w) ≤ (qw (E` using `E) n v false).ker := by`. Use `sup_le (fun c hc => MonoidHom.mem_ker.2 (hU c hc v (Finset.mem_insert_of_mem hv))) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, -, rfl⟩`.

Conclude with `MonoidHom.mem_ker.2 (pLoc_locGL_of_ne hvw a)`. Conclude with `MonoidHom.mem_ker.1 (hle hk)`. Establish `hy' : ∀ k ∈ U ⊔ (KGL w n).map (locGL E n w), finRep E n k y.1 = y.1`. Introduce `k hk`. Establish `hle : U ⊔ (KGL w n).map (locGL E n w) ≤ fixer y.1`.

Use `sup_le (fun c hc => ?_) ?_` and prove the remaining obligations. Conclude with `(finPart_val π c y).symm.trans (congrArg Subtype.val (mem_fix.1 hyU c hc))`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `(locRep_val π w a y).symm.trans (congrArg Subtype.val (mem_fix.1 hyK a ha))`. Conclude with `hle hk`.

Take `⟨φ, hφ, hφ0, hφU, hφP⟩` from `ih (fun v hv => hsat v (Finset.mem_insert_of_mem hv)) _ hU' ⟨y.1, y.2, fun e => hy0 (Subtype.ext e), hy'⟩`. Use `⟨φ, hφ, hφ0, fun k hk => hφU k (Subgroup.mem_sup_left hk), fun v hv => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hv with rfl | hv` into its components or cases. Conclude with `mem_fix.2 fun a ha => hφU _ (Subgroup.mem_sup_right ⟨a, ha, rfl⟩)`. Conclude with `hφP v hv`.
-/
theorem jointFix_pf : SlotBasic → JointFix := by
  intro _ E _ _ _ n π P
  classical
  induction P using Finset.induction_on with
  | empty =>
    rintro - U - ⟨ψ, h1, h2, h3⟩
    exact ⟨ψ, h1, h2, h3, by simp⟩
  | insert w P hw ih =>
    rintro hsat U hU ⟨ψ, hψ, h0, hfix⟩
    obtain ⟨B, hB⟩ := hsat w (Finset.mem_insert_self _ _)
    obtain ⟨y, hy0, hyU, hyK⟩ := step π w B hB U (fun k hk => hU k hk w (Finset.mem_insert_self _ _)) ⟨ψ, hψ⟩
      (fun e => h0 (congrArg Subtype.val e))
      (mem_fix.2 fun k hk => Subtype.ext ((finPart_val π k ⟨ψ, hψ⟩).trans (hfix k hk)))
    have hU' : ∀ k ∈ U ⊔ (KGL w n).map (locGL E n w), ∀ v ∈ P, qw n v false k = 1 := by
      intro k hk v hv
      have hvw : v ≠ w := fun e => hw (e ▸ hv)
      have hle : U ⊔ (KGL w n).map (locGL E n w) ≤ (qw (E := E) n v false).ker := by
        refine sup_le (fun c hc => MonoidHom.mem_ker.2 (hU c hc v (Finset.mem_insert_of_mem hv))) ?_
        rintro _ ⟨a, -, rfl⟩
        exact MonoidHom.mem_ker.2 (pLoc_locGL_of_ne hvw a)
      exact MonoidHom.mem_ker.1 (hle hk)
    have hy' : ∀ k ∈ U ⊔ (KGL w n).map (locGL E n w), finRep E n k y.1 = y.1 := by
      intro k hk
      have hle : U ⊔ (KGL w n).map (locGL E n w) ≤ fixer y.1 := by
        refine sup_le (fun c hc => ?_) ?_
        · exact (finPart_val π c y).symm.trans (congrArg Subtype.val (mem_fix.1 hyU c hc))
        · rintro _ ⟨a, ha, rfl⟩
          exact (locRep_val π w a y).symm.trans (congrArg Subtype.val (mem_fix.1 hyK a ha))
      exact hle hk
    obtain ⟨φ, hφ, hφ0, hφU, hφP⟩ := ih (fun v hv => hsat v (Finset.mem_insert_of_mem hv)) _ hU'
      ⟨y.1, y.2, fun e => hy0 (Subtype.ext e), hy'⟩
    refine ⟨φ, hφ, hφ0, fun k hk => hφU k (Subgroup.mem_sup_left hk), fun v hv => ?_⟩
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact mem_fix.2 fun a ha => hφU _ (Subgroup.mem_sup_right ⟨a, ha, rfl⟩)
    · exact hφP v hv

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
