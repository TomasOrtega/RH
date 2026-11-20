import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt.TypesOfLabels

private noncomputable def chRep {H : Type} [Group H] (χ : H →* ℂˣ) : Representation ℂ H ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem chRep_apply {H : Type} [Group H] (χ : H →* ℂˣ) (g : H) (z : ℂ) :
    chRep χ g z = ((χ g : ℂˣ) : ℂ) • z := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem trace_chRep {H : Type} [Group H] (χ : H →* ℂˣ) (g : H) :
    LinearMap.trace ℂ ℂ (chRep χ g) = ((χ g : ℂˣ) : ℂ) := by
  show LinearMap.trace ℂ ℂ (((χ g : ℂˣ) : ℂ) • LinearMap.id) = _
  rw [map_smul, LinearMap.trace_id]
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
private theorem isCl_trace {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) : IsCl (fun g => LinearMap.trace ℂ W (ρ g)) := by
  intro x y
  simp only [map_mul]
  rw [LinearMap.trace_mul_cycle, ← map_mul, mul_inv_cancel, map_one, one_mul]

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem trace_zero {W : Type} [AddCommGroup W] [Module ℂ W] (h : ¬ FiniteDimensional ℂ W) :
    LinearMap.trace ℂ W = 0 := by
  ext f
  have hn : ¬ ∃ s : Finset W, Nonempty (Module.Basis s ℂ W) := by
    rintro ⟨s, ⟨b⟩⟩
    exact h (Module.Finite.of_basis b)
  simp only [LinearMap.trace, dif_neg hn]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem ofFn_comp_get {β : Type} (M : List (ℕ × ℕ)) (f : ℕ × ℕ → β) :
    List.ofFn (fun a : Fin M.length => f (M.get a)) = M.map f := by
  rw [List.ofFn_comp', List.ofFn_get]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem sum_fst (M : List (ℕ × ℕ)) : ∑ a : Fin M.length, (M.get a).1 = deg M := by
  unfold GlobalTheory.Shin.deg
  rw [← List.sum_ofFn]
  congr 1
  have := List.ofFn_comp' M.get Prod.fst
  simpa [List.ofFn_get] using this

end UpperTheory.Gal.InertialTypesAlt.TypesOfLabels

open UpperTheory.Gal.InertialTypesAlt.TypesOfLabels in
set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact.

Replace the relevant objects with their definitions. Apply an available result and prove the equalities needed to match it to the conclusion. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.InertialTypesAlt.typeOfLbl :
    MeetsIff → FrobL → JDEq → TypeOfLbl := by
  intro hMI hFL hJD k _ _ _ _ θ N V _ _ π b hb hL
  obtain ⟨_, _, hN, hmeet⟩ := hb
  have hd : ∑ a : Fin (b.D ++ b.L).length, ((b.D ++ b.L).get a).1 = N := by
    rw [sum_fst, hN]
    simp [Lbl.rk, GlobalTheory.Shin.deg, List.map_append, List.sum_append]
  let ω : Fin (b.D ++ b.L).length → 𝓀[k]ˣ →* ℂˣ := fun a =>
    (powMonoidHom ((b.D ++ b.L).get a).2).comp
      ((Units.map (θ : AlgebraicClosure 𝓀[k] →* ℂ)).comp
        (Units.map (algebraMap 𝓀[k] (AlgebraicClosure 𝓀[k])).toMonoidHom))
  refine ⟨(b.D ++ b.L).length, fun a => ((b.D ++ b.L).get a).1,
    fun a => ((b.D ++ b.L).get a).2, hd, ω, ?_, ?_, ?_⟩
  · rw [show (fun a : Fin (b.D ++ b.L).length => (((b.D ++ b.L).get a).1, ((b.D ++ b.L).get a).2))
        = (b.D ++ b.L).get from funext fun a => rfl, List.ofFn_get]
  · intro a u
    simp [ω]
  have hJ : JD θ b.D b.L N = hcL (List.ofFn fun i : Fin (b.D ++ b.L).length =>
      (⟨((b.D ++ b.L).get i).1, detc θ ((b.D ++ b.L).get i).1 ((b.D ++ b.L).get i).2⟩ :
        (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N := by
    rw [(hJD 𝓀[k] θ).1, ofFn_comp_get (b.D ++ b.L)
      (fun p => (⟨p.1, detc θ p.1 p.2⟩ : (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))), List.map_append]
    congr 2
    apply List.map_congr_left
    rintro ⟨p1, p2⟩ hp
    have h1 : p1 = 1 := hL _ hp
    subst h1
    rw [(hJD 𝓀[k] θ).2.1]
  obtain ⟨c0, hc0, hF⟩ := hFL 𝓀[k] (b.D ++ b.L).length (fun a => ((b.D ++ b.L).get a).1) N hd
  have hsum := hF (fun i => detc θ ((b.D ++ b.L).get i).1 ((b.D ++ b.L).get i).2)
    (fun g => LinearMap.trace ℂ _ (levelZero π g)) (isCl_trace _)
  have hne : ∑ᶠ p : parab 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd),
      star (∏ i, detc θ ((b.D ++ b.L).get i).1 ((b.D ++ b.L).get i).2
        (leviProj 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd) p i)) *
        LinearMap.trace ℂ _ (levelZero π (p : GL (Fin N) 𝓀[k])) ≠ 0 := by
    intro h0
    unfold Meets at hmeet
    rw [hJ, hsum, h0, mul_zero] at hmeet
    exact hmeet rfl
  have hfd : FiniteDimensional ℂ (fixed π (KOne k (Fin N))) := by
    by_contra hfd
    apply hne
    simp [trace_zero hfd]
  let χ := (UpperTheory.Gal.TypesAndIwahori.leviChar (fun a : Fin (b.D ++ b.L).length => Fin ((b.D ++ b.L).get a).1) ω).comp
    (leviProj 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd))
  have hm : Meets ((levelZero π).comp (parab 𝓀[k] (stdBlocks (fun a => ((b.D ++ b.L).get a).1) hd)).subtype)
      (fun g => LinearMap.trace ℂ ℂ (chRep χ g)) := by
    unfold Meets
    convert hne using 3 with p
    simp only [trace_chRep]
    simp [χ, ω, UpperTheory.Gal.TypesAndIwahori.leviChar_apply, detc]
  obtain ⟨f, hf0, hf⟩ := ((hMI _ _ ℂ _ _).2).1 hm
  have hf1 : f 1 ≠ 0 := fun h => hf0 (LinearMap.ext_ring (by simpa using h))
  refine ⟨(f 1 : V), by simpa using hf1, ?_⟩
  intro g
  obtain ⟨hK, hP⟩ := mem_levelPre.1 g.2
  have h2 := congrArg Subtype.val (hf ⟨redK k (Fin N) ⟨(g : GL (Fin N) k), hK⟩, hP⟩ 1)
  rw [chRep_apply, map_smul] at h2
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, levelZero_apply,
    Submodule.coe_smul] at h2
  rw [← h2]
  rfl
