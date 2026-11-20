import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RelIdxRestr

/- English proof (translation)
Repeatedly rewrite using `[Subgroup.index, ← Nat.card_pi]`. Use `Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)` and prove the remaining obligations. Rewrite using `[QuotientGroup.leftRel_pi]`.
-/
theorem index_pi_univ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

/- English proof (translation)
Use `set S : Finset V := (Filter.eventually_cofinite.1 hev).toFinset with hS`. Establish `hSm : ∀ v, v ∉ S → C v ≤ H v` using `fun v hv => by`. Assume the negation of the conclusion as `h; exact hv (by simpa [hS] using h)`. Use `set Cg := ⨅ v, (C v).comap (pf v)`. Use `set Hg := ⨅ v, (H v).comap (pf v)`.

Establish `hmemC : ∀ x : X, x ∈ Cg ↔ ∀ v, pf v x ∈ C v` using `fun x => by simp [Cg, Subgroup.mem_iInf]`. Establish `hmemH : ∀ x : X, x ∈ Hg ↔ ∀ v, pf v x ∈ H v` using `fun x => by simp [Hg, Subgroup.mem_iInf]`. Set `φ : Cg →* ∀ v : S, C v` to `MonoidHom.pi fun v => ((pf v).comp Cg.subtype).codRestrict (C v) fun x => (hmemC x).1 x.2 v`. Establish `hφ : ∀ x (v : S), ((φ x v : C v) : Y v) = pf v x` using `fun _ _ => rfl`. Establish `hsurj : Function.Surjective φ`.

Introduce `y`. Set `z : ∀ v, Y v` to `fun v => if h : v ∈ S then (y ⟨v, h⟩ : Y v) else 1`. Take `⟨x, -, hx⟩` from `hX.exists_eq (fun w => w.elim) z (GlobalTheory.RestrMeas.eventually_of_finset S fun v hv => by simp [z, hv, one_mem])`. Establish `hxC : x ∈ Cg` using `(hmemC x).2 fun v => by`. Rewrite using `[hx v]`.

Distinguish the cases in `h : v ∈ S`. Simplify using `only [z, dif_pos h]`. Conclude with `(y ⟨v, h⟩).2`. Simplify using `only [z, dif_neg h]`. Conclude with `one_mem _`.

Use `⟨⟨x, hxC⟩, funext fun v => Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hφ]`. Use `show pf v x = _`. Rewrite using `[hx v]`. Simplify using `[z, v.2]`.

Establish `hcomap : Hg.subgroupOf Cg = (Subgroup.pi Set.univ fun v : S => (H v).subgroupOf (C v)).comap φ`. Use extensionality with `x`. Simplify using `only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies, hmemH]`. Prove the components needed by the constructor for the conclusion. Introduce `h v`.

Conclude with `h v`. Introduce `h v`. Distinguish the cases in `hv : v ∈ S`. Conclude with `h ⟨v, hv⟩`. Conclude with `hSm v hv ((hmemC x).1 x.2 v)`.

Rewrite using `[Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj, index_pi_univ, finprod_eq_prod_of_mulSupport_subset (s := S)]`. Conclude with `(Finset.prod_coe_sort S fun v => (H v).relIndex (C v))`. Introduce `v hv`. Assume the negation of the conclusion as `h`. Conclude with `hv (Subgroup.relIndex_eq_one.2 (hSm v h))`.
-/
theorem relIndex_iInf_comap {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)]
    [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v))
    (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K) (C H : ∀ v, Subgroup (Y v))
    (_hfin : ∀ v, (H v).relIndex (C v) ≠ 0) (hev : ∀ᶠ v in cofinite, C v ≤ H v) :
    (⨅ v, (H v).comap (pf v)).relIndex (⨅ v, (C v).comap (pf v)) = ∏ᶠ v, (H v).relIndex (C v) := by
  classical
  set S : Finset V := (Filter.eventually_cofinite.1 hev).toFinset with hS
  have hSm : ∀ v, v ∉ S → C v ≤ H v := fun v hv => by
    by_contra h; exact hv (by simpa [hS] using h)
  set Cg := ⨅ v, (C v).comap (pf v)
  set Hg := ⨅ v, (H v).comap (pf v)
  have hmemC : ∀ x : X, x ∈ Cg ↔ ∀ v, pf v x ∈ C v := fun x => by simp [Cg, Subgroup.mem_iInf]
  have hmemH : ∀ x : X, x ∈ Hg ↔ ∀ v, pf v x ∈ H v := fun x => by simp [Hg, Subgroup.mem_iInf]
  let φ : Cg →* ∀ v : S, C v := MonoidHom.pi fun v =>
    ((pf v).comp Cg.subtype).codRestrict (C v) fun x => (hmemC x).1 x.2 v
  have hφ : ∀ x (v : S), ((φ x v : C v) : Y v) = pf v x := fun _ _ => rfl
  have hsurj : Function.Surjective φ := by
    intro y
    let z : ∀ v, Y v := fun v => if h : v ∈ S then (y ⟨v, h⟩ : Y v) else 1
    obtain ⟨x, -, hx⟩ := hX.exists_eq (fun w => w.elim) z
      (GlobalTheory.RestrMeas.eventually_of_finset S fun v hv => by simp [z, hv, one_mem])
    have hxC : x ∈ Cg := (hmemC x).2 fun v => by
      rw [hx v]
      by_cases h : v ∈ S
      · simp only [z, dif_pos h]; exact (y ⟨v, h⟩).2
      · simp only [z, dif_neg h]; exact one_mem _
    refine ⟨⟨x, hxC⟩, funext fun v => Subtype.ext ?_⟩
    rw [hφ]
    show pf v x = _
    rw [hx v]
    simp [z, v.2]
  have hcomap : Hg.subgroupOf Cg = (Subgroup.pi Set.univ fun v : S => (H v).subgroupOf (C v)).comap φ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies, hmemH]
    constructor
    · intro h v; exact h v
    · intro h v
      by_cases hv : v ∈ S
      · exact h ⟨v, hv⟩
      · exact hSm v hv ((hmemC x).1 x.2 v)
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj, index_pi_univ,
    finprod_eq_prod_of_mulSupport_subset (s := S)]
  · exact (Finset.prod_coe_sort S fun v => (H v).relIndex (C v))
  · intro v hv
    by_contra h
    exact hv (Subgroup.relIndex_eq_one.2 (hSm v h))

end GlobalTheory.RelIdxRestr

end
