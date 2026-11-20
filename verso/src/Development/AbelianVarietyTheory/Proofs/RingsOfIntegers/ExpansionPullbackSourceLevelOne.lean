import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEInst
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSecKIsUnit
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UnifPreGenericFibreSurjectiveAppTopAndIsIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedCrossIdentityGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionCommutesPullbackCmEndoFourLeStatement

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullLevelOne

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Conclude with `pow_eq_zero_iff (n := 4) (by norm_num) |>.1 (by simpa using h₄)`. Use `mul_left_cancel₀ (pow_ne_zero 4 hy) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_of_pow_four_five {R : Type*} [CommRing R] [IsDomain R] {x y : R} (h₄ : x ^ 4 = y ^ 4)
    (h₅ : x ^ 5 = y ^ 5) : x = y := by
  by_cases hy : y = 0
  · subst hy
    exact pow_eq_zero_iff (n := 4) (by norm_num) |>.1 (by simpa using h₄)
  · refine mul_left_cancel₀ (pow_ne_zero 4 hy) ?_
    calc y ^ 4 * x = x ^ 5 := by rw [← h₄]; ring
      _ = y ^ 4 * y := by rw [h₅]; ring

/- English proof (translation)
Take `⟨u, hu, hc, hr⟩` from `h`. Establish `hL` using `U.LG.isLB`. Use `⟨fun y J => (val u (𝟙 _) y J).val, fun y J hJ => ?_, fun m t => ?_⟩` and prove the remaining obligations. Use `(secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 hr _ (𝟙 _) y J hJ` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Then use the resulting hypothesis.

Take `⟨v, hv, hvv⟩` from `exists_gen hL (φ' := ![gK, endK f ≫ gK]) (ε' := ![((m * N : ℕ) : ℤ), -(m : ℤ)]) (fun W _ h => by`. Simplify using `[Fin.prod_univ_two])`. Use the proof step `(GeneratorPullback.powGen U.LG.L _ _ u m) (powGen_isGen_of_isGen u hu m)`. Take `⟨t', ht'⟩` from `exists_sec hL (φ' := fun _ : Fin 1 => gK) (ε' := fun _ => ((m * N : ℕ) : ℤ)) (fun W _ h => by`. Simplify using `[Fin.prod_univ_two, Fintype.prod_sum_type, mul_left_comm])`.

Use the proof step `(pullMulSec t (endK f) v hv)`. Establish `key : ∀ y J, Good U.LG.L y J → sval t' (𝟙 _) y J = sval t (𝟙 _ ≫ endK f) y J * (val v (𝟙 _) y J).val` using `fun y J hJ => by`. Rewrite using `[ht' _ _ y J hJ, sval_pullMulSec _ _ _ _ _ y hJ]`. Use `⟨t', ⟨v, hv, ?_, (secRel_iff hL _ _ _ _ _ _ _ _ _ _).2 key⟩, fun y J hJ => ?_⟩` and prove the remaining obligations. Use `corr_of_val hL fun z J hJ => ?_` and prove the remaining obligations.

Establish `e` using `val_corr hJ hc (𝟙 _)`. Rewrite `e` using `[val_pull hJ, val_pull hJ, val_pow]`. Rewrite using `[val_pull hJ, val_pull hJ, val_pow, hvv _ _ z J hJ, val_pow, e, ← pow_mul, Nat.one_mul, Nat.mul_comm]`. Rewrite using `[key y J hJ, Category.id_comp, hvv _ _ y J hJ, val_pow, Units.val_pow_eq_pow_val]`.
-/
theorem exists_pull_pow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal V) D A G) (f : G ⟶ G) (N : ℕ) (s : U.SecK 1) (s' : U.SecK (1 * N))
    (h : IsPullByEnd U f 1 N s s') :
    ∃ c : ∀ y : (pullback G.hom (jK V) : Scheme.{0}), ((pullback G.hom (jK V) ⟶ G.left) → U.LG.L.ι) →
        (pullback G.hom (jK V) : Scheme.{0}).presheaf.stalk y,
      (∀ y J, Good U.LG.L y J → sval s' (𝟙 _) y J = sval s (endK f) y J * c y J) ∧
      ∀ (m : ℕ) (t : U.SecK m), ∃ t' : U.SecK (m * N), IsPullByEnd U f m N t t' ∧
        ∀ y J, Good U.LG.L y J → sval t' (𝟙 _) y J = sval t (endK f) y J * c y J ^ m := by
  obtain ⟨u, hu, hc, hr⟩ := h
  have hL := U.LG.isLB
  refine ⟨fun y J => (val u (𝟙 _) y J).val, fun y J hJ => ?_, fun m t => ?_⟩
  · have := (secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 hr _ (𝟙 _) y J hJ
    rwa [Category.id_comp] at this
  · obtain ⟨v, hv, hvv⟩ := exists_gen hL (φ' := ![gK, endK f ≫ gK]) (ε' := ![((m * N : ℕ) : ℤ), -(m : ℤ)])
      (fun W _ h => by
        simp [Fin.prod_univ_two])
      (GeneratorPullback.powGen U.LG.L _ _ u m) (powGen_isGen_of_isGen u hu m)
    obtain ⟨t', ht'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => gK) (ε' := fun _ => ((m * N : ℕ) : ℤ))
      (fun W _ h => by
        simp [Fin.prod_univ_two, Fintype.prod_sum_type, mul_left_comm])
      (pullMulSec t (endK f) v hv)
    have key : ∀ y J, Good U.LG.L y J →
        sval t' (𝟙 _) y J = sval t (𝟙 _ ≫ endK f) y J * (val v (𝟙 _) y J).val := fun y J hJ => by
      rw [ht' _ _ y J hJ, sval_pullMulSec _ _ _ _ _ y hJ]
    refine ⟨t', ⟨v, hv, ?_, (secRel_iff hL _ _ _ _ _ _ _ _ _ _).2 key⟩, fun y J hJ => ?_⟩
    · refine corr_of_val hL fun z J hJ => ?_
      have e := val_corr hJ hc (𝟙 _)
      rw [val_pull hJ, val_pull hJ, val_pow] at e
      rw [val_pull hJ, val_pull hJ, val_pow, hvv _ _ z J hJ, val_pow, e, ← pow_mul, Nat.one_mul, Nat.mul_comm]
    · rw [key y J hJ, Category.id_comp, hvv _ _ y J hJ, val_pow, Units.val_pow_eq_pow_val]

/- English proof (translation)
Introduce `hLaws V _ _ _ E _ _ _ H t P a N hN hN0`. Set `` to `H.starRing`. Introduce `s F hs s' hs'`. Take `⟨uΨ, huΨ, -, -⟩` from `P.w0`. Establish `hM : P.D.toPre.P.L.IsLB` using `P.D.toPre.P.isLB`.

Take `⟨F', hF'⟩` from `exists_pullAl P.D (FractionRing V) hM P.oD H.w0 uΨ huΨ a N hN hN0 1 F (pullSecs_fe' P.D (FractionRing V) hLaws.globalFns hM P.oD H.w0 P.w0 uΨ huΨ a N hN hN0 1 F)`. Take `⟨s'', hs'', -⟩` from `(P.U.expand (1 * N) (by omega)).2 F'`. Take `⟨c, hc, hpow⟩` from `exists_pull_pow P.U _ N s s' hs'`. Establish `hint` using `(GlobalTheory.unifPre_genericFibre_surjective_appTop_and_isIntegral hLaws.globalFns V _ _ _ _ P.U.toUnifPre).2`. Establish `e : s'' = s'`.

Use `SecOps.sec_ext (sec_ext_val P.U.LG.isLB fun y J hJ => ?_)` and prove the remaining obligations. Establish `hm : ∀ m : ℕ, 4 ≤ m → sval s'' (𝟙 _) y J ^ m = sval s' (𝟙 _) y J ^ m` using `fun m hm => by`. Take `⟨τ, hτ⟩` from `GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ _ _ _ P.U.toUnifPre m hm _ (endK (t.act.act a)) y J hJ`. Take `⟨τ', hτ', hv⟩` from `hpow m τ`. Take `⟨T, hT, -⟩` from `(P.U.expand m (by omega)).1 τ`.

Take `⟨T', hT', hTT⟩` from `GlobalTheory.T.expansion_commutes_pullback_cmEndo_four_le hLaws V E H t P a N hN hN0 m hm τ T hT τ' hτ'`. Establish `g` using `GlobalTheory.T.mixed_cross_identity_genericFibre hLaws V E H t P a N hN hN0 1 s F s'' F' hs hs'' hF' m τ T τ' T' hT hT' hTT m 1 (by ring) y J hJ`. Rewrite `g` using `[pow_one, pow_one, hv y J hJ]`. Use `hτ.mul_right_cancel (g.trans ?_)` and prove the remaining obligations. Rewrite using `[hc y J hJ]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `eq_of_pow_four_five (hm 4 le_rfl) (hm 5 (by norm_num))`. Conclude with `⟨F', e ▸ hs'', hF'⟩`.
-/
theorem expands_pull_level_one : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (s : P.U.SecK 1) (F : Fam P.D.toPre (FractionRing V) 1), P.U.Expands 1 s F → ∀ s' : P.U.SecK (1 * N), IsPullByEnd P.U (t.act.act a) 1 N s s' → ∃ F' : Fam P.D.toPre (FractionRing V) (1 * N), P.U.Expands (1 * N) s' F' ∧ PullAl P.D (FractionRing V) P.oD a 1 N F F' := by
  intro hLaws V _ _ _ E _ _ _ H t P a N hN hN0
  let := H.starRing
  intro s F hs s' hs'
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  have hM : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  obtain ⟨F', hF'⟩ := exists_pullAl P.D (FractionRing V) hM P.oD H.w0 uΨ huΨ a N hN hN0 1 F
    (pullSecs_fe' P.D (FractionRing V) hLaws.globalFns hM P.oD H.w0 P.w0 uΨ huΨ a N hN hN0 1 F)
  obtain ⟨s'', hs'', -⟩ := (P.U.expand (1 * N) (by omega)).2 F'
  obtain ⟨c, hc, hpow⟩ := exists_pull_pow P.U _ N s s' hs'
  have hint := (GlobalTheory.unifPre_genericFibre_surjective_appTop_and_isIntegral hLaws.globalFns V _ _ _ _
    P.U.toUnifPre).2
  have e : s'' = s' := by
    refine SecOps.sec_ext (sec_ext_val P.U.LG.isLB fun y J hJ => ?_)
    have hm : ∀ m : ℕ, 4 ≤ m → sval s'' (𝟙 _) y J ^ m = sval s' (𝟙 _) y J ^ m := fun m hm => by
      obtain ⟨τ, hτ⟩ := GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ _ _ _ P.U.toUnifPre m hm _
        (endK (t.act.act a)) y J hJ
      obtain ⟨τ', hτ', hv⟩ := hpow m τ
      obtain ⟨T, hT, -⟩ := (P.U.expand m (by omega)).1 τ
      obtain ⟨T', hT', hTT⟩ := GlobalTheory.T.expansion_commutes_pullback_cmEndo_four_le hLaws V E H t P a N hN hN0 m hm τ T hT τ' hτ'
      have g := GlobalTheory.T.mixed_cross_identity_genericFibre hLaws V E H t P a N hN hN0 1 s F s'' F' hs hs'' hF' m τ T τ' T' hT hT' hTT m 1
        (by ring) y J hJ
      rw [pow_one, pow_one, hv y J hJ] at g
      refine hτ.mul_right_cancel (g.trans ?_)
      rw [hc y J hJ]
      ring
    exact eq_of_pow_four_five (hm 4 le_rfl) (hm 5 (by norm_num))
  exact ⟨F', e ▸ hs'', hF'⟩

end GlobalTheory.PullLevelOne
