import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgEqOfLeRightStabiliser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConst
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AvgRestr

/- English proof (translation)
Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (rStab u) x`. Rewrite using `[hk]`. Conclude with `k.2 x`.
-/
theorem apply_out_mk {G : Type} [Group G] (u : G → ℂ) (x : G) :
    u ((QuotientGroup.mk x : G ⧸ rStab u).out) = u x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (rStab u) x
  rw [hk]
  exact k.2 x

/- English proof (translation)
Use `set P : Subgroup (∀ i, G i) := Subgroup.pi Set.univ fun i => rStab (u i) with hP`. Use `set R : Subgroup H := P.comap π with hRdef`. Establish `hPi : P.index = ∏ i, (rStab (u i)).index`. Repeatedly rewrite using `[hP, Subgroup.index, ← Nat.card_pi]`. Use `Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)` and prove the remaining obligations.

Rewrite using `[QuotientGroup.leftRel_pi]`. Establish `hRi : R.index = ∏ i, (rStab (u i)).index`. Rewrite using `[hRdef, Subgroup.index_comap_of_surjective _ hπ, hPi]`. Establish `hR0 : R.index ≠ 0` using `by rw [hRi]; exact Finset.prod_ne_zero_iff.2 fun i _ => hu i`. Establish `hRle : R ≤ rStab (fun k => ∏ i, u i (π k i))`.

Introduce `k hk x`. Establish `hk' : ∀ i, π k i ∈ rStab (u i)` using `fun i => ((Subgroup.mem_pi _).1 hk) i (Set.mem_univ i)`. Simplify using `only [map_mul, Pi.mul_apply]`. Conclude with `Finset.prod_congr rfl fun i _ => hk' i (π x i)`. Rewrite using `[avg_eq_of_le_rStab H _ R hRle hR0]`.

Use `haveI : R.FiniteIndex := ⟨hR0⟩`. Use `haveI : ∀ i, (rStab (u i)).FiniteIndex := fun i => ⟨hu i⟩`. Use `haveI : Fintype (H ⧸ R) := Fintype.ofFinite _`. Use `haveI : ∀ i, Fintype (G i ⧸ rStab (u i)) := fun i => Fintype.ofFinite _`. Set `e : H ⧸ R → ∀ i, G i ⧸ rStab (u i)` to `fun q i => QuotientGroup.mk (π q.out i)`.

Establish `he : Function.Bijective e`. Prove the components needed by the constructor for the conclusion. Introduce `q q' hq`. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']`. Apply `QuotientGroup.eq.2` to reduce the goal to its premises.

Use `show π (q.out⁻¹ * q'.out) ∈ P`. Use `(Subgroup.mem_pi _).2 fun i _ => ?_` and prove the remaining obligations. Use `QuotientGroup.eq.1 (congrFun hq i)` as an intermediate fact. Simplify `this` using `[map_mul, map_inv]`. Introduce `x`.

Take `⟨k, hk⟩` from `hπ fun i => (x i).out`. Use `⟨QuotientGroup.mk k, funext fun i => ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `QuotientGroup.mk_out_eq_mul R k`. Establish `hr' : π r ∈ P` using `r.2`. Use `show (QuotientGroup.mk (π (QuotientGroup.mk k : H ⧸ R).out i) : G i ⧸ rStab (u i)) = x i`.

Rewrite using `[hr, map_mul, Pi.mul_apply, hk]`. Use `conv_rhs => rw [← QuotientGroup.out_eq' (x i)]`. Apply `QuotientGroup.eq.2` to reduce the goal to its premises. Simplify using `using ((Subgroup.mem_pi _).1 hr') i (Set.mem_univ i)`. Establish `hsum : ∑ᶠ q : H ⧸ R, ∏ i, u i (π q.out i) = ∏ i, ∑ᶠ q : G i ⧸ rStab (u i), u i q.out`.

Rewrite using `[finsum_eq_sum_of_fintype]`. Repeatedly rewrite using `[finsum_eq_sum_of_fintype]`. Rewrite using `[Fintype.prod_sum]`. Conclude with `Fintype.sum_bijective e he _ _ fun q => Finset.prod_congr rfl fun i _ => (apply_out_mk (u i) _).symm`. Rewrite using `[hsum, hRi]`.

Simplify using `only [avg]`. Rewrite using `[Finset.prod_mul_distrib]`. Use `push_cast`. Rewrite using `[Finset.prod_inv_distrib]`.
-/
theorem avg_pi_comp {H : Type} [Group H] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    (π : H →* ∀ i, G i) (hπ : Function.Surjective π) (u : ∀ i, G i → ℂ) (hu : ∀ i, (rStab (u i)).index ≠ 0) :
    avg (fun k => ∏ i, u i (π k i)) = ∏ i, avg (u i) := by
  set P : Subgroup (∀ i, G i) := Subgroup.pi Set.univ fun i => rStab (u i) with hP
  set R : Subgroup H := P.comap π with hRdef
  have hPi : P.index = ∏ i, (rStab (u i)).index := by
    simp_rw [hP, Subgroup.index, ← Nat.card_pi]
    refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
    rw [QuotientGroup.leftRel_pi]
  have hRi : R.index = ∏ i, (rStab (u i)).index := by
    rw [hRdef, Subgroup.index_comap_of_surjective _ hπ, hPi]
  have hR0 : R.index ≠ 0 := by rw [hRi]; exact Finset.prod_ne_zero_iff.2 fun i _ => hu i
  have hRle : R ≤ rStab (fun k => ∏ i, u i (π k i)) := by
    intro k hk x
    have hk' : ∀ i, π k i ∈ rStab (u i) := fun i => ((Subgroup.mem_pi _).1 hk) i (Set.mem_univ i)
    simp only [map_mul, Pi.mul_apply]
    exact Finset.prod_congr rfl fun i _ => hk' i (π x i)
  rw [avg_eq_of_le_rStab H _ R hRle hR0]
  haveI : R.FiniteIndex := ⟨hR0⟩
  haveI : ∀ i, (rStab (u i)).FiniteIndex := fun i => ⟨hu i⟩
  haveI : Fintype (H ⧸ R) := Fintype.ofFinite _
  haveI : ∀ i, Fintype (G i ⧸ rStab (u i)) := fun i => Fintype.ofFinite _
  let e : H ⧸ R → ∀ i, G i ⧸ rStab (u i) := fun q i => QuotientGroup.mk (π q.out i)
  have he : Function.Bijective e := by
    constructor
    · intro q q' hq
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      apply QuotientGroup.eq.2
      show π (q.out⁻¹ * q'.out) ∈ P
      refine (Subgroup.mem_pi _).2 fun i _ => ?_
      have := QuotientGroup.eq.1 (congrFun hq i)
      simpa [map_mul, map_inv] using this
    · intro x
      obtain ⟨k, hk⟩ := hπ fun i => (x i).out
      refine ⟨QuotientGroup.mk k, funext fun i => ?_⟩
      obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul R k
      have hr' : π r ∈ P := r.2
      show (QuotientGroup.mk (π (QuotientGroup.mk k : H ⧸ R).out i) : G i ⧸ rStab (u i)) = x i
      rw [hr, map_mul, Pi.mul_apply, hk]
      conv_rhs => rw [← QuotientGroup.out_eq' (x i)]
      apply QuotientGroup.eq.2
      simpa using ((Subgroup.mem_pi _).1 hr') i (Set.mem_univ i)
  have hsum : ∑ᶠ q : H ⧸ R, ∏ i, u i (π q.out i) = ∏ i, ∑ᶠ q : G i ⧸ rStab (u i), u i q.out := by
    rw [finsum_eq_sum_of_fintype]
    simp_rw [finsum_eq_sum_of_fintype]
    rw [Fintype.prod_sum]
    exact Fintype.sum_bijective e he _ _ fun q => Finset.prod_congr rfl fun i _ => (apply_out_mk (u i) _).symm
  rw [hsum, hRi]
  simp only [avg]
  rw [Finset.prod_mul_distrib]
  push_cast
  rw [Finset.prod_inv_distrib]

end GlobalTheory.AvgRestr

namespace GlobalTheory.AvgRestr

/- English proof (translation)
Introduce `X V Y _ _ _ _ pf K hX u hu hev`. Take `⟨S, hS⟩` from `GlobalTheory.RestrMeas.exists_finset_of_eventually hev`. Use `set Kg : Subgroup X := ⨅ v, (K v).comap (pf v) with hKg`. Set `π : Kg →* ∀ v : S, K v.1` to `MonoidHom.pi fun v => ((pf v.1).comp Kg.subtype).codRestrict (K v.1) fun k => Subgroup.mem_iInf.1 k.2 v.1`. Establish `hπ : Function.Surjective π`.

Introduce `y`. Set `z : ∀ v, Y v` to `fun v => if h : v ∈ S then (y ⟨v, h⟩ : Y v) else 1`. Establish `hz : ∀ v, z v ∈ K v` using `fun v => by`. Distinguish the cases in `h : v ∈ S`. Simplify using `only [z, dif_pos h]`.

Conclude with `(y ⟨v, h⟩).2`. Simplify using `only [z, dif_neg h]`. Conclude with `one_mem _`. Take `⟨x, -, hx⟩` from `hX.exists_eq (fun w => w.elim) z (Eventually.of_forall hz)`. Establish `hxK : x ∈ Kg` using `Subgroup.mem_iInf.2 fun v => by show pf v x ∈ K v`.

Rewrite using `[hx v]`. Conclude with `hz v`. Use `⟨⟨x, hxK⟩, funext fun v => Subtype.ext ?_⟩` and prove the remaining obligations. Use `show pf v.1 x = (y v : Y v.1)`. Rewrite using `[hx v.1]`.

Simplify using `[z, v.2]`. Establish `hF : (fun k : Kg => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) = fun k => ∏ v : S, u v.1 (π k v)`. Use function extensionality and compare the values at `k`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by_contra fun h => hv (hS v h _), ← Finset.prod_coe_sort S]`. Both sides reduce to the same expression.

Establish `hA : ∏ᶠ v, avg (u v) = ∏ v : S, avg (u v.1)`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by_contra fun h => hv ?_, ← Finset.prod_coe_sort S]`. Establish `hc : u v = fun _ => 1` using `funext (hS v h)`. Rewrite using `[hc]`. Conclude with `(GlobalTheory.AvgLin.avg_linear_translate_const _ (fun _ : K v => (1 : ℂ)) (fun _ => 1) 1 1 (by rw [← hc]; exact hu v) (by rw [← hc]; exact hu v)).2.2.2`.

Rewrite using `[hF, hA]`. Conclude with `avg_pi_comp π hπ (fun v : S => u v.1) fun v => hu v.1`.
-/
theorem avg_restr_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)]
    [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)),
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (u : ∀ v, K v → ℂ),
    (∀ v, (rStab (u v)).index ≠ 0) → (∀ᶠ v in cofinite, ∀ k, u v k = 1) →
    avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) =
      ∏ᶠ v, avg (u v) := by
  intro X V Y _ _ _ _ pf K hX u hu hev
  obtain ⟨S, hS⟩ := GlobalTheory.RestrMeas.exists_finset_of_eventually hev
  set Kg : Subgroup X := ⨅ v, (K v).comap (pf v) with hKg
  let π : Kg →* ∀ v : S, K v.1 := MonoidHom.pi fun v =>
    ((pf v.1).comp Kg.subtype).codRestrict (K v.1) fun k => Subgroup.mem_iInf.1 k.2 v.1
  have hπ : Function.Surjective π := by
    intro y
    let z : ∀ v, Y v := fun v => if h : v ∈ S then (y ⟨v, h⟩ : Y v) else 1
    have hz : ∀ v, z v ∈ K v := fun v => by
      by_cases h : v ∈ S
      · simp only [z, dif_pos h]; exact (y ⟨v, h⟩).2
      · simp only [z, dif_neg h]; exact one_mem _
    obtain ⟨x, -, hx⟩ := hX.exists_eq (fun w => w.elim) z (Eventually.of_forall hz)
    have hxK : x ∈ Kg := Subgroup.mem_iInf.2 fun v => by
      show pf v x ∈ K v
      rw [hx v]; exact hz v
    refine ⟨⟨x, hxK⟩, funext fun v => Subtype.ext ?_⟩
    show pf v.1 x = (y v : Y v.1)
    rw [hx v.1]
    simp [z, v.2]
  have hF : (fun k : Kg => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) =
      fun k => ∏ v : S, u v.1 (π k v) := by
    funext k
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by_contra fun h => hv (hS v h _),
      ← Finset.prod_coe_sort S]
    rfl
  have hA : ∏ᶠ v, avg (u v) = ∏ v : S, avg (u v.1) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by_contra fun h => hv ?_,
      ← Finset.prod_coe_sort S]
    have hc : u v = fun _ => 1 := funext (hS v h)
    rw [hc]
    exact (GlobalTheory.AvgLin.avg_linear_translate_const _ (fun _ : K v => (1 : ℂ)) (fun _ => 1) 1 1
      (by rw [← hc]; exact hu v) (by rw [← hc]; exact hu v)).2.2.2
  rw [hF, hA]
  exact avg_pi_comp π hπ (fun v : S => u v.1) fun v => hu v.1

end GlobalTheory.AvgRestr
