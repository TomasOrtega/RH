import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEqZeroOfLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafSectionLocallyFiniteCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootFreeActionFinsuppSumStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit

namespace GlobalTheory.EtC.KummerSplit

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `e1 : Sec.res k (resGen 1 ξ) = resGen 1 (ξ.map k.appTop.hom)`. Unfold `resGen`. Rewrite using `[sec_res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1]`. Rewrite using `[e1]`. Establish `e2` using `(GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.2.1 W (ζ.map k.appTop.hom) (ξ.map k.appTop.hom) a h`.

Simplify using `only [zpow_one] at e2`. Unfold `resGen`. Rewrite using `[e2]`. Conclude with `map_nsmul ((resι (ZMod q) (tw q 1)).hom.app (op W)).hom _ _`.
-/
theorem res_resGen_of_pow (q : ℕ) [NeZero q] {W V : Scheme.{0}} (k : W ⟶ V) (ζ ξ : Prim q Γ(V, ⊤)) (a : (ZMod q)ˣ)
    (h : k.appTop.hom ξ.1 = k.appTop.hom ζ.1 ^ (a : ZMod q).val) :
    Sec.res k (resGen 1 ξ) = (a : ZMod q).val • resGen 1 (ζ.map k.appTop.hom) := by
  have e1 : Sec.res k (resGen 1 ξ) = resGen 1 (ξ.map k.appTop.hom) := by
    unfold resGen
    rw [sec_res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1]
  rw [e1]
  have e2 := (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.2.1 W (ζ.map k.appTop.hom) (ξ.map k.appTop.hom) a h
  simp only [zpow_one] at e2
  unfold resGen
  rw [e2]
  exact map_nsmul ((resι (ZMod q) (tw q 1)).hom.app (op W)).hom _ _

end GlobalTheory.EtC.KummerSplit

namespace GlobalTheory.EtC.KummerSplit

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `set d : unitsP.obj (op V) →₀ ULift.{1} (ZMod q) := c.sum fun x r => Finsupp.single (unitsP.mk (tripP.get x).tgt) r - Finsupp.single (unitsP.mk (tripP.get x).src) r with hd_def`. Establish `hd : (d.sum fun u r => r • freeGen (ZMod q) unitsP V u) = 0`. Rewrite using `[← Finsupp.linearCombination_apply, hd_def, map_finsuppSum, ← hc]`. Use `Finsupp.sum_congr fun x _ => ?_` and prove the remaining obligations. Rewrite using `[map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, smul_sub]`.

Establish `hloc` using `(GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination (ZMod q) unitsP V).2 d hd`. Distinguish the cases in `hc0 : c = 0`. Simplify using `[hc0]`. Take `⟨x₀, -⟩` from `Finsupp.support_nonempty_iff.2 hc0`. Establish `hroots : ∀ x : ↥c.support, Loc V fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom (tripP.get x.1).root.1 = g.appTop.hom (tripP.get x₀).root.1 ^ (a : ZMod q).val` using `fun x => (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.1 (tripP.get x₀).root (tripP.get x.1).root`.

Establish `hall` using `loc_calculus.2.2.2.2.2.1 V (↥c.support) (fun x _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom (tripP.get x.1).root.1 = g.appTop.hom (tripP.get x₀).root.1 ^ (a : ZMod q).val) hroots`. Establish `hboth` using `loc_calculus.2.2.1 V _ _ hloc hall`. Apply `sec_eq_zero_of_loc` to reduce the goal to its premises. Use `loc_calculus.2.1 V _ _ hboth ?_` and prove the remaining obligations. Introduce and unpack `W k ⟨hkd, hka⟩`.

Rewrite using `[res_sum]`. Distinguish the cases in `hW : IsEmpty W`. Conclude with `sec_eq_zero_of_loc _ _ (loc_calculus.2.2.2.2.2.2 W _)`. Rewrite `hW` using `[not_isEmpty_iff]`. Use `haveI : Nontrivial Γ(W, ⊤) := @Scheme.component_nontrivial W ⊤ ⟨⟨hW.some, trivial⟩⟩`.

Use `choose a ha using hka`. Set `a' : (tripP q).obj (op V) → ℕ` to `fun x => if h : x ∈ c.support then ((a ⟨x, h⟩ : (ZMod q)ˣ) : ZMod q).val else 0`. Establish `hax : ∀ x (hx : x ∈ c.support), a' x = ((a ⟨x, hx⟩ : (ZMod q)ˣ) : ZMod q).val` using `fun x hx => dif_pos hx`. Establish `hsum : (c.sum fun x r => r • Sec.res k (resGen 1 (tripP.get x).root)) = (c.sum fun x r => r * ((a' x : ℕ) : ULift.{1} (ZMod q))) • resGen 1 ((tripP.get x₀).root.map k.appTop.hom)`. Rewrite using `[Finsupp.sum, Finsupp.sum, Finset.sum_smul]`.

Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[res_resGen_of_pow q k (tripP.get x₀).root _ (a ⟨x, hx⟩) (ha ⟨x, hx⟩), ← hax x hx, mul_smul, Nat.cast_smul_eq_nsmul]`. Establish `halg` using `GlobalTheory.T.primitiveRoot_free_action_finsupp_sum q Γ(W, ⊤) ((tripP.get x₀).root.map k.appTop.hom) ((tripP q).obj (op V)) c.support (fun x => c x) a' (fun x => Units.map k.appTop.hom.toMonoidHom (tripP.get x).src) (fun x => Units.map k.appTop.hom.toMonoidHom (tripP.get x).tgt) …`. Rewrite using `[hsum]`. It suffices to establish `h0 : (c.sum fun x r => r * ((a' x : ℕ) : ULift.{1} (ZMod q))) = 0 by rw [h0, zero_smul]`.

Apply `ULift.ext` to reduce the goal to its premises. Rewrite using `[Finsupp.sum]`. Use `Eq.trans ?_ halg` and prove the remaining obligations. Proceed by induction on `c.support using Finset.induction_on with`. Consider the case `empty => simp`.

Consider the case `insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ULift.add_down, ih]`. Simplify using the standard rewrite rules. Introduce `x hx`. Rewrite using `[hax x hx]`. Express the relevant statement in the definitionally equal form `k.appTop.hom ((tripP.get x).tgt : Γ(V, ⊤)) = k.appTop.hom (tripP.get x₀).root.1 ^ _ * k.appTop.hom ((tripP.get x).src : Γ(V, ⊤))`.

Rewrite using `[(tripP.get x).tgt_eq, map_mul, ha ⟨x, hx⟩]`. Rewrite `hkd` using `[hd_def, Finsupp.sum, Finsupp.mapDomain_finsetSum]`. Simplify using `only [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, unitsP.map_mk] at hkd`. Conclude with `hkd`.
-/
theorem relation_kernel (q : ℕ) [NeZero q] (V : Scheme.{0}) (c : (tripP q).obj (op V) →₀ ULift.{1} (ZMod q))
    (hc : (c.sum fun x r => r • (freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).tgt) -
      freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).src))) = 0) :
    (c.sum fun x r => r • resGen 1 (tripP.get x).root) = 0 := by
  classical
  set d : unitsP.obj (op V) →₀ ULift.{1} (ZMod q) :=
    c.sum fun x r => Finsupp.single (unitsP.mk (tripP.get x).tgt) r - Finsupp.single (unitsP.mk (tripP.get x).src) r
    with hd_def
  have hd : (d.sum fun u r => r • freeGen (ZMod q) unitsP V u) = 0 := by
    rw [← Finsupp.linearCombination_apply, hd_def, map_finsuppSum, ← hc]
    refine Finsupp.sum_congr fun x _ => ?_
    rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, smul_sub]
  have hloc := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination (ZMod q) unitsP V).2 d hd
  by_cases hc0 : c = 0
  · simp [hc0]
  obtain ⟨x₀, -⟩ := Finsupp.support_nonempty_iff.2 hc0
  have hroots : ∀ x : ↥c.support, Loc V fun _ g => ∃ a : (ZMod q)ˣ,
      g.appTop.hom (tripP.get x.1).root.1 = g.appTop.hom (tripP.get x₀).root.1 ^ (a : ZMod q).val :=
    fun x => (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.1 (tripP.get x₀).root (tripP.get x.1).root
  have hall := loc_calculus.2.2.2.2.2.1 V (↥c.support) (fun x _ g => ∃ a : (ZMod q)ˣ,
      g.appTop.hom (tripP.get x.1).root.1 = g.appTop.hom (tripP.get x₀).root.1 ^ (a : ZMod q).val) hroots
  have hboth := loc_calculus.2.2.1 V _ _ hloc hall
  apply sec_eq_zero_of_loc
  refine loc_calculus.2.1 V _ _ hboth ?_
  rintro W k ⟨hkd, hka⟩
  rw [res_sum]
  by_cases hW : IsEmpty W
  · exact sec_eq_zero_of_loc _ _ (loc_calculus.2.2.2.2.2.2 W _)
  rw [not_isEmpty_iff] at hW
  haveI : Nontrivial Γ(W, ⊤) := @Scheme.component_nontrivial W ⊤ ⟨⟨hW.some, trivial⟩⟩
  choose a ha using hka
  let a' : (tripP q).obj (op V) → ℕ := fun x =>
    if h : x ∈ c.support then ((a ⟨x, h⟩ : (ZMod q)ˣ) : ZMod q).val else 0
  have hax : ∀ x (hx : x ∈ c.support), a' x = ((a ⟨x, hx⟩ : (ZMod q)ˣ) : ZMod q).val := fun x hx => dif_pos hx
  have hsum : (c.sum fun x r => r • Sec.res k (resGen 1 (tripP.get x).root)) =
      (c.sum fun x r => r * ((a' x : ℕ) : ULift.{1} (ZMod q))) •
        resGen 1 ((tripP.get x₀).root.map k.appTop.hom) := by
    rw [Finsupp.sum, Finsupp.sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [res_resGen_of_pow q k (tripP.get x₀).root _ (a ⟨x, hx⟩) (ha ⟨x, hx⟩), ← hax x hx, mul_smul,
      Nat.cast_smul_eq_nsmul]
  have halg := GlobalTheory.T.primitiveRoot_free_action_finsupp_sum q Γ(W, ⊤) ((tripP.get x₀).root.map k.appTop.hom) ((tripP q).obj (op V)) c.support
    (fun x => c x) a'
    (fun x => Units.map k.appTop.hom.toMonoidHom (tripP.get x).src)
    (fun x => Units.map k.appTop.hom.toMonoidHom (tripP.get x).tgt) ?_ ?_
  · rw [hsum]
    suffices h0 : (c.sum fun x r => r * ((a' x : ℕ) : ULift.{1} (ZMod q))) = 0 by rw [h0, zero_smul]
    apply ULift.ext
    rw [Finsupp.sum]
    refine Eq.trans ?_ halg
    induction c.support using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ULift.add_down, ih]; simp
  · intro x hx
    rw [hax x hx]
    change k.appTop.hom ((tripP.get x).tgt : Γ(V, ⊤)) =
      k.appTop.hom (tripP.get x₀).root.1 ^ _ * k.appTop.hom ((tripP.get x).src : Γ(V, ⊤))
    rw [(tripP.get x).tgt_eq, map_mul, ha ⟨x, hx⟩]
  · rw [hd_def, Finsupp.sum, Finsupp.mapDomain_finsetSum] at hkd
    simp only [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, unitsP.map_mk] at hkd
    exact hkd

end GlobalTheory.EtC.KummerSplit
