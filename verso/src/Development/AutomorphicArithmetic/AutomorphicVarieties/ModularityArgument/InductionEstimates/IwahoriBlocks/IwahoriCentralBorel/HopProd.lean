import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.HopfProductGluing

private def dbl {G : Type} [Group G] (U : Subgroup G) (g : G) : Set (G ⧸ U) :=
  {c : G ⧸ U | ∃ u ∈ U, c = QuotientGroup.mk (u * g)}

/- English proof (translation)
Use `haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU.2`. Establish `hc : Continuous fun u : G => (QuotientGroup.mk (u * g) : G ⧸ U)` using `QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)`. Use `((hU.1.image hc).finite_of_discrete).subset ?_` and prove the remaining obligations. Introduce and unpack `c ⟨u, hu, rfl⟩`. Conclude with `⟨u, hu, rfl⟩`.
-/
private theorem dbl_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G}
    (hU : CO U) (g : G) : (dbl U g).Finite := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU.2
  have hc : Continuous fun u : G => (QuotientGroup.mk (u * g) : G ⧸ U) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hU.1.image hc).finite_of_discrete).subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

/- English proof (translation)
Establish `h1` using `hv _ (QuotientGroup.eq.1 h)`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem act_congr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {U : Subgroup G} {v : V} (hv : ∀ u ∈ U, ρ u v = v) {x y : G}
    (h : (QuotientGroup.mk x : G ⧸ U) = QuotientGroup.mk y) : ρ x v = ρ y v := by
  have h1 := hv _ (QuotientGroup.eq.1 h)
  calc ρ x v = ρ x (ρ (x⁻¹ * y) v) := by rw [h1]
    _ = ρ y v := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

variable {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)]

/- English proof (translation)
Simplify using `[QuotientGroup.eq, Subgroup.mem_pi]`.
-/
private theorem mk_eq (U : ∀ i, Subgroup (G i)) (x y : ∀ i, G i) :
    (QuotientGroup.mk x : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) = QuotientGroup.mk y ↔
      ∀ j, (QuotientGroup.mk (x j) : G j ⧸ U j) = QuotientGroup.mk (y j) := by
  simp [QuotientGroup.eq, Subgroup.mem_pi]

private noncomputable def pr (U : ∀ i, Subgroup (G i)) (j : Fin r) (c : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) : G j ⧸ U j :=
  QuotientGroup.mk (c.out j)

/- English proof (translation)
The claim follows from `(mk_eq U _ _).1 (QuotientGroup.out_eq' _) j`.
-/
private theorem pr_mk (U : ∀ i, Subgroup (G i)) (j : Fin r) (x : ∀ i, G i) :
    pr U j (QuotientGroup.mk x) = QuotientGroup.mk (x j) :=
  (mk_eq U _ _).1 (QuotientGroup.out_eq' _) j

/- English proof (translation)
Rewrite using `[← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d]`. Conclude with `(mk_eq U _ _).2 h`.
-/
private theorem pr_ext (U : ∀ i, Subgroup (G i)) {c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U}
    (h : ∀ j, pr U j c = pr U j d) : c = d := by
  rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d]
  exact (mk_eq U _ _).2 h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩ j`. Conclude with `⟨u j, hu j trivial, pr_mk U j _⟩`. Introduce `h choose u hu he using h`. Conclude with `⟨u, fun j _ => hu j, pr_ext U fun j => by rw [pr_mk]; exact he j⟩`.
-/
private theorem mem_dbl (U : ∀ i, Subgroup (G i)) (g : ∀ i, G i) (c : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) :
    c ∈ dbl (Subgroup.pi Set.univ U) g ↔ ∀ j, pr U j c ∈ dbl (U j) (g j) := by
  constructor
  · rintro ⟨u, hu, rfl⟩ j
    exact ⟨u j, hu j trivial, pr_mk U j _⟩
  · intro h
    choose u hu he using h
    exact ⟨u, fun j _ => hu j, pr_ext U fun j => by rw [pr_mk]; exact he j⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Simplify `hu` using `[QuotientGroup.eq]`. Introduce and unpack `rfl`. Conclude with `⟨1, U.one_mem, by simp⟩`.
-/
private theorem mem_dbl_one {H : Type} [Group H] (U : Subgroup H) (c : H ⧸ U) :
    c ∈ dbl U 1 ↔ c = QuotientGroup.mk 1 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [QuotientGroup.eq] using hu
  · rintro rfl
    exact ⟨1, U.one_mem, by simp⟩

private noncomputable def glue (U : ∀ i, Subgroup (G i)) (i : Fin r) (c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) :
    (∀ i, G i) ⧸ Subgroup.pi Set.univ U :=
  QuotientGroup.mk (Pi.mulSingle i (c.out i) * d.out)

/- English proof (translation)
Rewrite using `[glue, pr_mk]`. Use `QuotientGroup.eq.1 hd` as an intermediate fact. Simplify `this` using `[pr, QuotientGroup.eq]`.
-/
private theorem pr_glue_same (U : ∀ i, Subgroup (G i)) (i : Fin r) (c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U)
    (hd : pr U i d = QuotientGroup.mk 1) : pr U i (glue U i c d) = pr U i c := by
  rw [glue, pr_mk]
  have := QuotientGroup.eq.1 hd
  simpa [pr, QuotientGroup.eq] using this

/- English proof (translation)
Rewrite using `[glue, pr_mk]`. Simplify using `[pr, Pi.mulSingle_eq_of_ne h]`.
-/
private theorem pr_glue_ne (U : ∀ i, Subgroup (G i)) {i j : Fin r} (h : j ≠ i)
    (c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) : pr U j (glue U i c d) = pr U j d := by
  rw [glue, pr_mk]
  simp [pr, Pi.mulSingle_eq_of_ne h]

/- English proof (translation)
Establish `hW : CO (Subgroup.pi Set.univ U)` using `⟨isCompact_univ_pi fun j => (hU j).1, isOpen_set_pi Set.finite_univ fun j _ => (hU j).2⟩`. Establish `hs : ∀ g w, hopR ρ (Subgroup.pi Set.univ U) g w = ∑ c ∈ (dbl_finite hW g).toFinset, ρ c.out w` using `fun g w => finsum_mem_eq_finite_toFinset_sum _ (dbl_finite hW g)`. Establish `ha : ∀ c ∈ dbl (Subgroup.pi Set.univ U) (Pi.mulSingle i x), ∀ j, j ≠ i → pr U j c = QuotientGroup.mk 1`. Introduce `c hc j hj`. Use `(mem_dbl U _ c).1 hc j` as an intermediate fact.

Rewrite `this` using `[Pi.mulSingle_eq_of_ne hj, mem_dbl_one]`. Then use the resulting hypothesis. Establish `hb' : ∀ d ∈ dbl (Subgroup.pi Set.univ U) b, pr U i d = QuotientGroup.mk 1`. Introduce `d hd`. Use `(mem_dbl U _ d).1 hd i` as an intermediate fact. Rewrite `this` using `[hb, mem_dbl_one]`. Then use the resulting hypothesis.

Establish `h1 : hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i x) (hopR ρ (Subgroup.pi Set.univ U) b v) = ∑ p ∈ (dbl_finite hW (Pi.mulSingle i x)).toFinset ×ˢ (dbl_finite hW b).toFinset, ρ (glue U i p.1 p.2).out v`. Rewrite using `[hs (Pi.mulSingle i x), Finset.sum_product]`. Use `Finset.sum_congr rfl fun c hc => ?_` and prove the remaining obligations. Rewrite `hc` using `[Set.Finite.mem_toFinset]`. Establish `e : ρ c.out (hopR ρ (Subgroup.pi Set.univ U) b v) = ρ (Pi.mulSingle i (c.out i)) (hopR ρ (Subgroup.pi Set.univ U) b v)`.

Use `act_congr ρ hw ((mk_eq U _ _).2 fun j => ?_)` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Pi.mulSingle_eq_of_ne hj]`.

Conclude with `ha c hc j hj`. Rewrite using `[e, hs b, map_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Conclude with `act_congr ρ hv (QuotientGroup.out_eq' _).symm`.

Rewrite using `[h1, hs]`. Use `symm`. Use `Finset.sum_bij (fun p _ => glue U i p.1 p.2) ?_ ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce and unpack `⟨c, d⟩ hp`. Simplify using `only [Finset.mem_product, Set.Finite.mem_toFinset] at hp ⊢`.

Use `(mem_dbl U _ _).2 fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[pr_glue_same U j c d (hb' d hp.2), Pi.mul_apply, hb, mul_one]`. Conclude with `(mem_dbl U _ _).1 hp.1 j`.

Rewrite using `[pr_glue_ne U hj, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, one_mul]`. Conclude with `(mem_dbl U _ _).1 hp.2 j`. Introduce and unpack `⟨c, d⟩ hp ⟨c', d'⟩ hp' h`. Simplify using `only [Finset.mem_product, Set.Finite.mem_toFinset] at hp hp'`. Establish `h' : glue U i c d = glue U i c' d'` using `h`.

Use `Prod.ext (pr_ext U fun j => ?_) (pr_ext U fun j => ?_)` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[← pr_glue_same U j c d (hb' d hp.2), h', pr_glue_same U j c' d' (hb' d' hp'.2)]`. Rewrite using `[ha c hp.1 j hj, ha c' hp'.1 j hj]`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[hb' d hp.2, hb' d' hp'.2]`. Rewrite using `[← pr_glue_ne U hj c d, h', pr_glue_ne U hj]`. Introduce `e he`.

Rewrite `he` using `[Set.Finite.mem_toFinset, mem_dbl]`. Establish `hd : pr U i (QuotientGroup.mk (Function.update e.out i 1)) = QuotientGroup.mk 1`. Rewrite using `[pr_mk, Function.update_self]`. Use `⟨(QuotientGroup.mk (Pi.mulSingle i (e.out i)), QuotientGroup.mk (Function.update e.out i 1)), ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_product, Set.Finite.mem_toFinset, mem_dbl]`.

Use `⟨fun j => ?_, fun j => ?_⟩` and prove the remaining obligations. Use `he j` as an intermediate fact. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite `this` using `[Pi.mul_apply, hb, mul_one]`.

Rewrite using `[pr_mk, Pi.mulSingle_eq_same j (Quotient.out e j)]`. Conclude with `this`. Rewrite using `[pr_mk, Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, mem_dbl_one]`. Use `he j` as an intermediate fact. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Rewrite using `[hd, hb, mem_dbl_one]`. Rewrite `this` using `[Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, one_mul]`. Rewrite using `[pr_mk, Function.update_of_ne hj]`. Conclude with `this`.

Use `pr_ext U fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[pr_glue_same U j _ _ hd, pr_mk, Pi.mulSingle_eq_same]`. Both sides reduce to the same expression.

Rewrite using `[pr_glue_ne U hj, pr_mk, Function.update_of_ne hj]`. Both sides reduce to the same expression.
-/
private theorem hop_mul [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (∀ i, G i) V) (U : ∀ i, Subgroup (G i)) (hU : ∀ i, CO (U i))
    (i : Fin r) (x : G i) (b : ∀ i, G i) (hb : b i = 1) (v : V) (hv : ∀ u ∈ Subgroup.pi Set.univ U, ρ u v = v)
    (hw : ∀ u ∈ Subgroup.pi Set.univ U, ρ u (hopR ρ (Subgroup.pi Set.univ U) b v) = hopR ρ (Subgroup.pi Set.univ U) b v) :
    hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i x * b) v =
      hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i x) (hopR ρ (Subgroup.pi Set.univ U) b v) := by
  have hW : CO (Subgroup.pi Set.univ U) :=
    ⟨isCompact_univ_pi fun j => (hU j).1, isOpen_set_pi Set.finite_univ fun j _ => (hU j).2⟩
  have hs : ∀ g w, hopR ρ (Subgroup.pi Set.univ U) g w = ∑ c ∈ (dbl_finite hW g).toFinset, ρ c.out w :=
    fun g w => finsum_mem_eq_finite_toFinset_sum _ (dbl_finite hW g)
  have ha : ∀ c ∈ dbl (Subgroup.pi Set.univ U) (Pi.mulSingle i x), ∀ j, j ≠ i → pr U j c = QuotientGroup.mk 1 := by
    intro c hc j hj
    have := (mem_dbl U _ c).1 hc j
    rwa [Pi.mulSingle_eq_of_ne hj, mem_dbl_one] at this
  have hb' : ∀ d ∈ dbl (Subgroup.pi Set.univ U) b, pr U i d = QuotientGroup.mk 1 := by
    intro d hd
    have := (mem_dbl U _ d).1 hd i
    rwa [hb, mem_dbl_one] at this
  have h1 : hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i x) (hopR ρ (Subgroup.pi Set.univ U) b v) =
      ∑ p ∈ (dbl_finite hW (Pi.mulSingle i x)).toFinset ×ˢ (dbl_finite hW b).toFinset,
        ρ (glue U i p.1 p.2).out v := by
    rw [hs (Pi.mulSingle i x), Finset.sum_product]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Set.Finite.mem_toFinset] at hc
    have e : ρ c.out (hopR ρ (Subgroup.pi Set.univ U) b v) =
        ρ (Pi.mulSingle i (c.out i)) (hopR ρ (Subgroup.pi Set.univ U) b v) := by
      refine act_congr ρ hw ((mk_eq U _ _).2 fun j => ?_)
      by_cases hj : j = i
      · subst hj; simp
      · rw [Pi.mulSingle_eq_of_ne hj]; exact ha c hc j hj
    rw [e, hs b, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Module.End.mul_apply, ← map_mul]
    exact act_congr ρ hv (QuotientGroup.out_eq' _).symm
  rw [h1, hs]
  symm
  refine Finset.sum_bij (fun p _ => glue U i p.1 p.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨c, d⟩ hp
    simp only [Finset.mem_product, Set.Finite.mem_toFinset] at hp ⊢
    refine (mem_dbl U _ _).2 fun j => ?_
    by_cases hj : j = i
    · subst hj
      rw [pr_glue_same U j c d (hb' d hp.2), Pi.mul_apply, hb, mul_one]
      exact (mem_dbl U _ _).1 hp.1 j
    · rw [pr_glue_ne U hj, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, one_mul]
      exact (mem_dbl U _ _).1 hp.2 j
  · rintro ⟨c, d⟩ hp ⟨c', d'⟩ hp' h
    simp only [Finset.mem_product, Set.Finite.mem_toFinset] at hp hp'
    have h' : glue U i c d = glue U i c' d' := h
    refine Prod.ext (pr_ext U fun j => ?_) (pr_ext U fun j => ?_)
    · by_cases hj : j = i
      · subst hj
        rw [← pr_glue_same U j c d (hb' d hp.2), h', pr_glue_same U j c' d' (hb' d' hp'.2)]
      · rw [ha c hp.1 j hj, ha c' hp'.1 j hj]
    · by_cases hj : j = i
      · subst hj
        rw [hb' d hp.2, hb' d' hp'.2]
      · rw [← pr_glue_ne U hj c d, h', pr_glue_ne U hj]
  · intro e he
    rw [Set.Finite.mem_toFinset, mem_dbl] at he
    have hd : pr U i (QuotientGroup.mk (Function.update e.out i 1)) = QuotientGroup.mk 1 := by
      rw [pr_mk, Function.update_self]
    refine ⟨(QuotientGroup.mk (Pi.mulSingle i (e.out i)), QuotientGroup.mk (Function.update e.out i 1)), ?_, ?_⟩
    · simp only [Finset.mem_product, Set.Finite.mem_toFinset, mem_dbl]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have := he j
        by_cases hj : j = i
        · subst hj
          rw [Pi.mul_apply, hb, mul_one] at this
          rw [pr_mk, Pi.mulSingle_eq_same j (Quotient.out e j)]
          exact this
        · rw [pr_mk, Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, mem_dbl_one]
      · have := he j
        by_cases hj : j = i
        · subst hj
          rw [hd, hb, mem_dbl_one]
        · rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, one_mul] at this
          rw [pr_mk, Function.update_of_ne hj]
          exact this
    · refine pr_ext U fun j => ?_
      by_cases hj : j = i
      · subst hj
        rw [pr_glue_same U j _ _ hd, pr_mk, Pi.mulSingle_eq_same]
        rfl
      · rw [pr_glue_ne U hj, pr_mk, Function.update_of_ne hj]
        rfl

/- English proof (translation)
Establish `h : dbl U 1 = {QuotientGroup.mk 1}` using `Set.ext fun c => mem_dbl_one U c`. Express the relevant statement in the definitionally equal form `∑ᶠ c ∈ dbl U 1, ρ c.out v = v`. Rewrite using `[h, finsum_mem_singleton, act_congr ρ hv (QuotientGroup.out_eq' _), map_one, Module.End.one_apply]`.
-/
private theorem hop_one {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    {U : Subgroup H} {v : V} (hv : ∀ u ∈ U, ρ u v = v) : hopR ρ U 1 v = v := by
  have h : dbl U 1 = {QuotientGroup.mk 1} := Set.ext fun c => mem_dbl_one U c
  change ∑ᶠ c ∈ dbl U 1, ρ c.out v = v
  rw [h, finsum_mem_singleton, act_congr ρ hv (QuotientGroup.out_eq' _), map_one, Module.End.one_apply]

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.HopfProductGluing

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.HopfProductGluing in
/- English proof (translation)
Introduce `r G _ _ _ V _ _ ρ U Q hU hfix hone`. Establish `key : ∀ s : Finset (Fin r), ∀ g : ∀ i, G i, (∀ j, j ∉ s → g j = 1) → ∀ v ∈ Q, hopR ρ (Subgroup.pi Set.univ U) g v ∈ Q`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Introduce `g hg v hv`. Establish `: g = 1` using `funext fun j => hg j (Finset.notMem_empty j)`. Rewrite using `[this, hop_one ρ (hfix v hv)]`. Conclude with `hv`. Consider the case `insert i s hi ih`.

Introduce `g hg v hv`. Establish `hb : hopR ρ (Subgroup.pi Set.univ U) (Function.update g i 1) v ∈ Q`. Use `ih _ (fun j hj => ?_) v hv` and prove the remaining obligations. Distinguish the cases in `hji : j = i`. Substitute `hji` using the available equality.

Conclude with `Function.update_self ..`. Rewrite using `[Function.update_of_ne hji]`. Conclude with `hg j (by simp [hji, hj])`. Establish `e : g = Pi.mulSingle i (g i) * Function.update g i 1`. Use function extensionality and compare the values at `j`.

Distinguish the cases in `hji : j = i`. Substitute `hji` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.mulSingle_eq_of_ne hji, Function.update_of_ne hji]`. Rewrite using `[e, hop_mul ρ U hU i (g i) _ (Function.update_self ..) v (hfix v hv) (hfix _ hb)]`.

Conclude with `hone i _ _ hb`. Conclude with `fun g => key Finset.univ g (fun j hj => absurd (Finset.mem_univ j) hj)`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.hopProd :
    ∀ {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (∀ i, G i) V) (U : ∀ i, Subgroup (G i)) (Q : Submodule ℂ V), (∀ i, CO (U i)) →
      (∀ v ∈ Q, ∀ u ∈ Subgroup.pi Set.univ U, ρ u v = v) → (∀ i g, ∀ v ∈ Q, hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i g) v ∈ Q) →
      ∀ g, ∀ v ∈ Q, hopR ρ (Subgroup.pi Set.univ U) g v ∈ Q := by
  intro r G _ _ _ V _ _ ρ U Q hU hfix hone
  have key : ∀ s : Finset (Fin r), ∀ g : ∀ i, G i, (∀ j, j ∉ s → g j = 1) →
      ∀ v ∈ Q, hopR ρ (Subgroup.pi Set.univ U) g v ∈ Q := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg v hv
      have : g = 1 := funext fun j => hg j (Finset.notMem_empty j)
      rw [this, hop_one ρ (hfix v hv)]
      exact hv
    | insert i s hi ih =>
      intro g hg v hv
      have hb : hopR ρ (Subgroup.pi Set.univ U) (Function.update g i 1) v ∈ Q := by
        refine ih _ (fun j hj => ?_) v hv
        by_cases hji : j = i
        · subst hji; exact Function.update_self ..
        · rw [Function.update_of_ne hji]
          exact hg j (by simp [hji, hj])
      have e : g = Pi.mulSingle i (g i) * Function.update g i 1 := by
        funext j
        by_cases hji : j = i
        · subst hji; simp
        · simp [Pi.mulSingle_eq_of_ne hji, Function.update_of_ne hji]
      rw [e, hop_mul ρ U hU i (g i) _ (Function.update_self ..) v (hfix v hv) (hfix _ hb)]
      exact hone i _ _ hb
  exact fun g => key Finset.univ g (fun j hj => absurd (Finset.mem_univ j) hj)
