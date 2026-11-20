import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedH1CardInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualEvalBidualApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerModPrimePowInjectsResidualSelmerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualSelmerClassesGiveNoncohomologousCochainsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardOrdinaryLocalConditionModPrimePowLeConstMulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGaloisInvariantsOrdinaryRankTwoModPowBoundedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ArchimedeanInvariantsCardStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwIneq

/- English proof (translation)
Establish `h : ∀ w : InfinitePlace ℚ, ∃ c : G ℚ Ω, w.IsReal → IsCCAt w c` using `fun w => by`. Distinguish the cases in `hw : w.IsReal`. Use `haveI : Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic haveI : IsGalois ℚ Ω := {}`. Use `letI : Algebra ℚ ℂ := w.embedding.toAlgebra`. Set `j : Ω →ₐ[ℚ] ℂ` to `IsAlgClosed.lift`.

Establish `hr : ComplexEmbedding.IsReal w.embedding` using `InfinitePlace.isReal_iff.1 hw`. Set `cj : ℂ →ₐ[ℚ] ℂ` to `{ starRingEnd ℂ with commutes' := fun x => RingHom.congr_fun hr x }`. Use `letI : Algebra Ω ℂ := j.toRingHom.toAlgebra`. Use `haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm`. Use `⟨(cj.comp j).restrictNormal' Ω, fun _ => ⟨j.toRingHom, fun x => ?_, ?_⟩⟩` and prove the remaining obligations.

Conclude with `AlgHom.restrictNormal_commutes (cj.comp j) Ω x`. Rewrite using `[show j.toRingHom.comp (algebraMap ℚ Ω) = w.embedding from RingHom.ext fun x => j.commutes x]`. Conclude with `w.mk_embedding`. Conclude with `⟨1, fun h => absurd h hw⟩`. Use `choose cc hcc using h`.

Conclude with `⟨cc, hcc⟩`.
-/
theorem exists_cc (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] :
    ∃ cc : InfinitePlace ℚ → G ℚ Ω, ∀ w, w.IsReal → IsCCAt w (cc w) := by
  have h : ∀ w : InfinitePlace ℚ, ∃ c : G ℚ Ω, w.IsReal → IsCCAt w c := fun w => by
    by_cases hw : w.IsReal
    · haveI : Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree
      haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
      haveI : IsGalois ℚ Ω := {}
      letI : Algebra ℚ ℂ := w.embedding.toAlgebra
      let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
      have hr : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.1 hw
      let cj : ℂ →ₐ[ℚ] ℂ := { starRingEnd ℂ with commutes' := fun x => RingHom.congr_fun hr x }
      letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
      haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
      refine ⟨(cj.comp j).restrictNormal' Ω, fun _ => ⟨j.toRingHom, fun x => ?_, ?_⟩⟩
      · exact AlgHom.restrictNormal_commutes (cj.comp j) Ω x
      · rw [show j.toRingHom.comp (algebraMap ℚ Ω) = w.embedding from RingHom.ext fun x => j.commutes x]
        exact w.mk_embedding
    · exact ⟨1, fun h => absurd h hw⟩
  choose cc hcc using h
  exact ⟨cc, hcc⟩

/- English proof (translation)
Introduce `hL l _ Ω _ _ _ e S A W hW c hint`. Establish `hN` using `kills_NS hW`. Take `⟨C0, hC0⟩` from `GlobalTheory.T.card_galoisInvariants_ordinaryRankTwo_mod_pow_bounded l Ω e S A W hW c hint hN`. Take `⟨CA, hCA⟩` from `GlobalTheory.T.card_ordinaryLocalConditionModPrimePow_le_const_mul hL l Ω e S A W hW c hint hN`. Use `⟨C0 * CA, fun n hn N y hy hyd => ?_⟩` and prove the remaining obligations.

Establish `hn0 : 0 < n` using `hn`. Establish `hS` using `hW.above`. Take `⟨μ, hμ⟩` from `GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := n) (S := S) hS`. Take `⟨cc, hcc⟩` from `exists_cc Ω`. Establish `hρ : ReciprocityTheory.Gal.ContAction (rhoS c n W hint S hN)` using `contAction_rhoS c n W hint S hN hW.cont`.

Establish `hgw` using `hL.gw ℚ Ω l n (Mn c n) S (rhoS c n W hint S hN) hn0 hW.l_odd hS hρ μ hμ (Av A S) (isPlaceOver_Av A S) cc hcc (Lc c n W hint S hN A)`. Establish `hρd : ReciprocityTheory.Gal.ContAction (twDual μ (rhoS c n W hint S hN))` using `GlobalTheory.DualSide.contAction_twDual (GlobalTheory.Published.PoitouTate.contAction_charRep hμ) hρ`. Use `haveI : Finite (TDual (ZMod (l ^ n)) (Mn c n)) := GlobalTheory.DualSide.finite_TDual`. Use `haveI : Finite (H1 (rhoS c n W hint S hN)) := (hL.gf ℚ Ω l n (Mn c n) S _ hn0 hS hρ).2.1`. Use `haveI : Finite (H1 (twDual μ (rhoS c n W hint S hN))) := (hL.gf ℚ Ω l n (TDual (ZMod (l ^ n)) (Mn c n)) S _ hn0 hS hρd).2.1`.

Take `⟨v0, hA0, hl0⟩` from `hW.atL`. Set `vA : S` to `⟨v0, hS v0 hl0⟩`. Establish `huniq : ∀ v w : Pl, IsPlaceOver A v → IsPlaceOver A w → v = w` using `fun v w hv hw => HeightOneSpectrum.ext (Ideal.ext fun x => (hv x).symm.trans (hw x))`. Establish `hLv : ∀ v : S, v ≠ vA → Nat.card (Lc c n W hint S hN A v) = Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v)))`. Introduce `v hv`.

Establish `hnp : ¬ IsPlaceOver A v.1` using `fun h => hv (Subtype.ext (huniq _ _ h hA0))`. Establish `e1 : Lc c n W hint S hN A v = H1ur ((rhoS c n W hint S hN).comp (locFam S (Av A S) v)) ((Ine (F` using `ℚ) (Av A S v)).subgroupOf (Dec (F := ℚ) (Av A S v))) := if_neg hnp`. Rewrite using `[e1]`. Conclude with `GlobalTheory.Ord2.UrCard.card_unramified_h1_eq_card_h0 ℚ Ω l n (Mn c n) (Av A S v) v.1 _ (hρ.comp' (continuous_locFam S (Av A S) v)) (isPlaceOver_Av A S v)`. Establish `harch` using `GlobalTheory.T.archimedean_invariants_card l Ω e S A W hW c hint hN n hn cc hcc`.

Rewrite `hgw` using `[harch, ← Finset.mul_prod_erase _ _ (Finset.mem_univ vA), ← Finset.mul_prod_erase _ _ (Finset.mem_univ vA), Finset.prod_congr rfl fun v hv => hLv v (Finset.ne_of_mem_erase hv)]`. Establish `hLA` using `hCA n hn vA hA0`. Establish `hH0` using `hC0 n hn`. Establish `hP : 0 < ∏ v ∈ Finset.univ.erase vA, Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v)))` using `Finset.prod_pos fun v _ => Nat.card_pos`. Establish `hq : 0 < Nat.card (Qn c n)` using `Nat.card_pos`.

Establish `h1d : 1 ≤ Nat.card (H0 (twDual μ (rhoS c n W hint S hN)))` using `Nat.card_pos`. Establish `h1A : 1 ≤ Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) vA)))` using `Nat.card_pos`. Use `set P := ∏ v ∈ Finset.univ.erase vA, Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v)))`. Establish `hsel : Nat.card (SelG c n W hint S hN A) ≤ C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ)`. Establish `key : Nat.card (SelG c n W hint S hN A) * (Nat.card (Qn c n) * P) ≤ (C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ)) * (Nat.card (Qn c n) * P)`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `Nat.le_of_mul_le_mul_right key (Nat.mul_pos hq hP)`. Take `⟨cls, hcls, hinj⟩` from `GlobalTheory.T.ordinarySelmerModPrimePow_injects_residualSelmer l Ω e S A W hW c hint hN n hn`. Establish `hN1 : N ≤ Nat.card (SelG c n W hint S hN A)`. Set `f : Fin N → SelG c n W hint S hN A` to `fun i => ⟨cls (y i), hcls _ (hy i)⟩`.

Establish `hf : Function.Injective f`. Introduce `i j hij`. Assume the negation of the conclusion as `hne`. Conclude with `hyd i j hne (hinj _ _ (hy i) (hy j) (congrArg Subtype.val hij))`. Simplify using `using Nat.card_le_card_of_injective f hf`.

Take `⟨z, hz, hzd⟩` from `GlobalTheory.T.dualSelmer_classes_give_noncohomologous_cochains hL l Ω e S A W hW c hint hN n hn μ hμ`. Set `eqv` to `Finite.equivFin (SelD c n W hint S hN A hW.cont μ)`. Use `⟨Nat.card (SelD c n W hint S hN A hW.cont μ), fun i => z (eqv.symm i), ?_, fun i => hz _, ?_⟩` and prove the remaining obligations. Conclude with `hN1.trans hsel`. Introduce `i j hij`.

Conclude with `hzd _ _ (fun h => hij (eqv.symm.injective h))`.
-/
theorem gw_ineq : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (y : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A W (y i)) → (∀ i j, i ≠ j → ¬ Cob1 c n W ⊤ (y i - y j)) → ∃ (N' : ℕ) (z : Fin N' → G ℚ Ω → Fin 2 → Qbar l), N ≤ C * N' ∧ (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) ∧ ∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j) := by
  classical
  intro hL l _ Ω _ _ _ e S A W hW c hint
  have hN := kills_NS hW
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.card_galoisInvariants_ordinaryRankTwo_mod_pow_bounded l Ω e S A W hW c hint hN
  obtain ⟨CA, hCA⟩ := GlobalTheory.T.card_ordinaryLocalConditionModPrimePow_le_const_mul hL l Ω e S A W hW c hint hN
  refine ⟨C0 * CA, fun n hn N y hy hyd => ?_⟩
  have hn0 : 0 < n := hn
  have hS := hW.above
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := n) (S := S) hS
  obtain ⟨cc, hcc⟩ := exists_cc Ω
  have hρ : ReciprocityTheory.Gal.ContAction (rhoS c n W hint S hN) := contAction_rhoS c n W hint S hN hW.cont
  have hgw := hL.gw ℚ Ω l n (Mn c n) S (rhoS c n W hint S hN) hn0 hW.l_odd hS hρ μ hμ (Av A S)
    (isPlaceOver_Av A S) cc hcc (Lc c n W hint S hN A)
  have hρd : ReciprocityTheory.Gal.ContAction (twDual μ (rhoS c n W hint S hN)) :=
    GlobalTheory.DualSide.contAction_twDual (GlobalTheory.Published.PoitouTate.contAction_charRep hμ) hρ
  haveI : Finite (TDual (ZMod (l ^ n)) (Mn c n)) := GlobalTheory.DualSide.finite_TDual
  haveI : Finite (H1 (rhoS c n W hint S hN)) := (hL.gf ℚ Ω l n (Mn c n) S _ hn0 hS hρ).2.1
  haveI : Finite (H1 (twDual μ (rhoS c n W hint S hN))) :=
    (hL.gf ℚ Ω l n (TDual (ZMod (l ^ n)) (Mn c n)) S _ hn0 hS hρd).2.1

  obtain ⟨v0, hA0, hl0⟩ := hW.atL
  let vA : S := ⟨v0, hS v0 hl0⟩
  have huniq : ∀ v w : Pl, IsPlaceOver A v → IsPlaceOver A w → v = w := fun v w hv hw =>
    HeightOneSpectrum.ext (Ideal.ext fun x => (hv x).symm.trans (hw x))
  have hLv : ∀ v : S, v ≠ vA → Nat.card (Lc c n W hint S hN A v) =
      Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))) := by
    intro v hv
    have hnp : ¬ IsPlaceOver A v.1 := fun h => hv (Subtype.ext (huniq _ _ h hA0))
    have e1 : Lc c n W hint S hN A v = H1ur ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))
        ((Ine (F := ℚ) (Av A S v)).subgroupOf (Dec (F := ℚ) (Av A S v))) := if_neg hnp
    rw [e1]
    exact GlobalTheory.Ord2.UrCard.card_unramified_h1_eq_card_h0 ℚ Ω l n (Mn c n) (Av A S v) v.1 _
      (hρ.comp' (continuous_locFam S (Av A S) v)) (isPlaceOver_Av A S v)
  have harch := GlobalTheory.T.archimedean_invariants_card l Ω e S A W hW c hint hN n hn cc hcc
  rw [harch, ← Finset.mul_prod_erase _ _ (Finset.mem_univ vA),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ vA),
    Finset.prod_congr rfl fun v hv => hLv v (Finset.ne_of_mem_erase hv)] at hgw
  have hLA := hCA n hn vA hA0
  have hH0 := hC0 n hn
  have hP : 0 < ∏ v ∈ Finset.univ.erase vA, Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))) :=
    Finset.prod_pos fun v _ => Nat.card_pos
  have hq : 0 < Nat.card (Qn c n) := Nat.card_pos
  have h1d : 1 ≤ Nat.card (H0 (twDual μ (rhoS c n W hint S hN))) := Nat.card_pos
  have h1A : 1 ≤ Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) vA))) := Nat.card_pos
  set P := ∏ v ∈ Finset.univ.erase vA, Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v)))
  have hsel : Nat.card (SelG c n W hint S hN A) ≤ C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ) := by
    have key : Nat.card (SelG c n W hint S hN A) * (Nat.card (Qn c n) * P) ≤
        (C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ)) * (Nat.card (Qn c n) * P) := by
      calc Nat.card (SelG c n W hint S hN A) * (Nat.card (Qn c n) * P)
          = Nat.card (SelG c n W hint S hN A) * 1 * (1 * P) * Nat.card (Qn c n) := by ring
        _ ≤ Nat.card (SelG c n W hint S hN A) * Nat.card (H0 (twDual μ (rhoS c n W hint S hN))) *
            (Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) vA))) * P) * Nat.card (Qn c n) := by
          gcongr
        _ = Nat.card (SelD c n W hint S hN A hW.cont μ) * Nat.card (H0 (rhoS c n W hint S hN)) *
            (Nat.card (Lc c n W hint S hN A vA) * P) := hgw
        _ ≤ Nat.card (SelD c n W hint S hN A hW.cont μ) * C0 * (CA * Nat.card (Qn c n) * P) := by
          gcongr
        _ = (C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ)) * (Nat.card (Qn c n) * P) := by ring
    exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hq hP)

  obtain ⟨cls, hcls, hinj⟩ := GlobalTheory.T.ordinarySelmerModPrimePow_injects_residualSelmer l Ω e S A W hW c hint hN n hn
  have hN1 : N ≤ Nat.card (SelG c n W hint S hN A) := by
    let f : Fin N → SelG c n W hint S hN A := fun i => ⟨cls (y i), hcls _ (hy i)⟩
    have hf : Function.Injective f := by
      intro i j hij
      by_contra hne
      exact hyd i j hne (hinj _ _ (hy i) (hy j) (congrArg Subtype.val hij))
    simpa using Nat.card_le_card_of_injective f hf

  obtain ⟨z, hz, hzd⟩ := GlobalTheory.T.dualSelmer_classes_give_noncohomologous_cochains hL l Ω e S A W hW c hint hN n hn μ hμ
  let eqv := Finite.equivFin (SelD c n W hint S hN A hW.cont μ)
  refine ⟨Nat.card (SelD c n W hint S hN A hW.cont μ), fun i => z (eqv.symm i), ?_, fun i => hz _, ?_⟩
  · exact hN1.trans hsel
  · intro i j hij
    exact hzd _ _ (fun h => hij (eqv.symm.injective h))

end GlobalTheory.Ord2.GwIneq
