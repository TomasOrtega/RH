import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrigVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedValueAtOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedValueAtOriginMemIdealPowOfVanishesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitRigidifiedValueAtOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumNullFamilyCompleteLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedValueAtOriginPullbackDegenerationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOriginValuesSumModPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ hB D C k hk b₀ hb₀ F₀ hL`. Use `choose v hv using fun α => GlobalTheory.T.exists_rigidifiedValueAtOrigin R D.toPre k α (F₀.f α)`. Establish `hvm : ∀ α e, VanMod (maximalIdeal R) (F₀.f α) e → v α ∈ maximalIdeal R ^ (e + 1)` using `fun α e h => GlobalTheory.T.rigidifiedValueAtOrigin_mem_idealPow_of_vanishes R _ D.toPre k α (F₀.f α) (v α) e (hv α) h`. Establish `hfin : ∀ e : ℕ, {α | v α ∉ maximalIdeal R ^ (e + 1)}.Finite` using `fun e => (F₀.small e).subset fun α h h' => h (hvm α e h')`. Take `⟨s, hs⟩` from `GlobalTheory.T.exists_adicSum_null_family_complete_local R hB D.toPre.X v hfin`.

Use `⟨s, ?_, ?_⟩` and prove the remaining obligations. Establish `hv0 : IsUnit (v 0)`. Establish `h0` using `hv 0`. Rewrite `h0` using `[hL.1]`. Conclude with `GlobalTheory.T.isUnit_rigidifiedValueAtOrigin R D.toPre k 0 b₀ (v 0) h0 hb₀`.

Establish `h1 : s - v 0 ∈ maximalIdeal R`. Use `hs 0 {0} (fun α hα => hvm α 0 (hL.2 α (by simpa using hα)))` as an intermediate fact. Simplify using `using this`. Assume the negation of the conclusion as `hn`. Establish `hs' : s ∈ maximalIdeal R` using `(mem_maximalIdeal s).2 hn`.

Establish `: v 0 ∈ maximalIdeal R`. Use `(maximalIdeal R).sub_mem hs' h1` as an intermediate fact. Simplify using `using this`. Conclude with `((mem_maximalIdeal _).1 this) hv0`. Introduce `W _ _ _ T σ' f' hP hE J' hJ'`.

Establish `hw : ∀ x, OrigVal T.D'.toPre (f' x) (T.φ (v (T.hD.xe x)))` using `fun x => GlobalTheory.T.rigidifiedValueAtOrigin_pullback_degeneration R W T.φ D.toPre T.D'.toPre T.hD k x (F₀.f (T.hD.xe x)) (f' x) (v (T.hD.xe x)) (hP x) (hv _)`. Use `haveI : IsLocalHom T.φ := T.loc`. Establish `hmap : ∀ e, (maximalIdeal R ^ (e + 1)).map T.φ ≤ maximalIdeal W ^ (e + 1)` using `fun e => by`. Rewrite using `[Ideal.map_pow]`. Use `Ideal.pow_right_mono ?_ _` and prove the remaining obligations.

Use `Ideal.map_le_iff_le_comap.2 fun x hx => (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal x).1 hx (isUnit_of_map_unit T.φ x hu)` and prove the remaining obligations. Establish `step : ∀ e : ℕ, ∃ c ∈ maximalIdeal W ^ (e + 1), sval σ' (unitW T.G) (cpt W) J' = stalkOf (cpt W) (T.φ s + c) * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k`. Introduce `e`. Take `⟨S, hS, hc⟩` from `GlobalTheory.T.expansion_originValues_sum_modPow W T.D' T.A T.G T.U.toUnifPre k e σ' f' _ hw (hE e)`. Take `⟨c, hcm, heq⟩` from `hc J' hJ'`.

Set `S1 : Finset D.toPre.X` to `S.map T.hD.xe.toEquiv.toEmbedding`. Set `S2 : Finset D.toPre.X` to `S1 ∪ (hfin e).toFinset`. Establish `h2` using `hs e S2 (fun α hα => by`. Assume the negation of the conclusion as `h`. Conclude with `hα (Finset.mem_union_right _ ((hfin e).mem_toFinset.2 h)))`.

Establish `hsum1 : ∑ x ∈ S, T.φ (v (T.hD.xe x)) = T.φ (∑ α ∈ S1, v α)`. Simplify using `[S1, map_sum]`. Establish `hdiff : T.φ (∑ α ∈ S2, v α) - T.φ (∑ α ∈ S1, v α) ∈ maximalIdeal W ^ (e + 1)`. Rewrite using `[← map_sub, ← Finset.sum_sdiff (Finset.subset_union_left : S1 ⊆ S2), add_sub_cancel_right, map_sum]`. Use `Ideal.sum_mem _ fun α hα => ?_` and prove the remaining obligations.

Establish `hα1 : α ∉ S1` using `(Finset.mem_sdiff.1 hα).2`. Use `hS (T.hD.xe.symm α) (fun hx => hα1 (by` as an intermediate fact. Simplify using `only [S1, Finset.mem_map_equiv]`. Simplify using `using hx))`. Simplify using `using this`.

Establish `h2' : T.φ s - T.φ (∑ α ∈ S2, v α) ∈ maximalIdeal W ^ (e + 1)`. Rewrite using `[← map_sub]`. Conclude with `hmap e (Ideal.mem_map_of_mem _ h2)`. Use `⟨c - (T.φ s - T.φ (∑ α ∈ S2, v α)) - (T.φ (∑ α ∈ S2, v α) - T.φ (∑ α ∈ S1, v α)), Ideal.sub_mem _ (Ideal.sub_mem _ hcm h2') hdiff, ?_⟩` and prove the remaining obligations. Rewrite using `[heq, hsum1]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Use `haveI : IsDiscreteValuationRing W := ((GlobalTheory.LN.cDvr_iff W).1 T.cdvr).1`. Use `choose c hc heq using step`. Establish `hce : ∀ e, c e = c 0` using `fun e => by`.

Use `(heq e).symm.trans (heq 0)` as an intermediate fact. Establish `hu` using `(Units.isUnit ((val T.U.LG.rig (idW W) (cpt W) J') ^ k))`. Rewrite `hu` using `[Units.val_pow_eq_pow_val]`. Use `hu.mul_right_cancel this` as an intermediate fact. Apply `add_left_cancel (a := T.φ s)` to reduce the goal to its premises.

Apply `stalkOf_injective (cpt W)` to reduce the goal to its premises. Conclude with `this`. Establish `h0 : c 0 = 0`. Establish `hm : c 0 ∈ ⨅ n : ℕ, maximalIdeal W ^ n` using `Submodule.mem_iInf _ |>.2 fun n => by`. Break down `n with _ | n` into its components or cases.

Simplify using the standard rewrite rules. Rewrite using `[← hce n]`. Conclude with `hc n`. Rewrite `hm` using `[Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal W) (maximalIdeal.isMaximal W).ne_top, Submodule.mem_bot]`. Then use the resulting hypothesis. Rewrite using `[heq 0, h0, add_zero]`.
-/
theorem exists_unit_origin_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ b₀ : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b₀ → ∀ F₀ : IntFam (maximalIdeal R) D.toPre k, F₀.Lead 0 b₀ → ∃ s₀ : R, IsUnit s₀ ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (σ' : H0 T.U.LG.L k) (f' : ∀ x, T.D'.toPre.SecB k x), (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → (∀ e, T.U.ExpandsAt e k σ' f') → ∀ J', Good T.U.LG.L (cpt W) J' → sval σ' (unitW T.G) (cpt W) J' = stalkOf (cpt W) (T.φ s₀) * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k := by
  intro R _ _ _ hB D C k hk b₀ hb₀ F₀ hL
  choose v hv using fun α => GlobalTheory.T.exists_rigidifiedValueAtOrigin R D.toPre k α (F₀.f α)
  have hvm : ∀ α e, VanMod (maximalIdeal R) (F₀.f α) e → v α ∈ maximalIdeal R ^ (e + 1) :=
    fun α e h => GlobalTheory.T.rigidifiedValueAtOrigin_mem_idealPow_of_vanishes R _ D.toPre k α (F₀.f α) (v α) e (hv α) h
  have hfin : ∀ e : ℕ, {α | v α ∉ maximalIdeal R ^ (e + 1)}.Finite := fun e =>
    (F₀.small e).subset fun α h h' => h (hvm α e h')
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_adicSum_null_family_complete_local R hB D.toPre.X v hfin
  refine ⟨s, ?_, ?_⟩
  · have hv0 : IsUnit (v 0) := by
      have h0 := hv 0
      rw [hL.1] at h0
      exact GlobalTheory.T.isUnit_rigidifiedValueAtOrigin R D.toPre k 0 b₀ (v 0) h0 hb₀
    have h1 : s - v 0 ∈ maximalIdeal R := by
      have := hs 0 {0} (fun α hα => hvm α 0 (hL.2 α (by simpa using hα)))
      simpa using this
    by_contra hn
    have hs' : s ∈ maximalIdeal R := (mem_maximalIdeal s).2 hn
    have : v 0 ∈ maximalIdeal R := by
      have := (maximalIdeal R).sub_mem hs' h1
      simpa using this
    exact ((mem_maximalIdeal _).1 this) hv0
  · intro W _ _ _ T σ' f' hP hE J' hJ'
    have hw : ∀ x, OrigVal T.D'.toPre (f' x) (T.φ (v (T.hD.xe x))) := fun x =>
      GlobalTheory.T.rigidifiedValueAtOrigin_pullback_degeneration R W T.φ D.toPre T.D'.toPre T.hD k x (F₀.f (T.hD.xe x)) (f' x) (v (T.hD.xe x)) (hP x) (hv _)
    haveI : IsLocalHom T.φ := T.loc
    have hmap : ∀ e, (maximalIdeal R ^ (e + 1)).map T.φ ≤ maximalIdeal W ^ (e + 1) := fun e => by
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ _
      refine Ideal.map_le_iff_le_comap.2 fun x hx => (mem_maximalIdeal _).2 fun hu =>
        (mem_maximalIdeal x).1 hx (isUnit_of_map_unit T.φ x hu)
    have step : ∀ e : ℕ, ∃ c ∈ maximalIdeal W ^ (e + 1),
        sval σ' (unitW T.G) (cpt W) J' = stalkOf (cpt W) (T.φ s + c) * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k := by
      intro e
      obtain ⟨S, hS, hc⟩ := GlobalTheory.T.expansion_originValues_sum_modPow W T.D' T.A T.G T.U.toUnifPre k e σ' f' _ hw (hE e)
      obtain ⟨c, hcm, heq⟩ := hc J' hJ'
      classical
      let S1 : Finset D.toPre.X := S.map T.hD.xe.toEquiv.toEmbedding
      let S2 : Finset D.toPre.X := S1 ∪ (hfin e).toFinset
      have h2 := hs e S2 (fun α hα => by
        by_contra h
        exact hα (Finset.mem_union_right _ ((hfin e).mem_toFinset.2 h)))
      have hsum1 : ∑ x ∈ S, T.φ (v (T.hD.xe x)) = T.φ (∑ α ∈ S1, v α) := by
        simp [S1, map_sum]
      have hdiff : T.φ (∑ α ∈ S2, v α) - T.φ (∑ α ∈ S1, v α) ∈ maximalIdeal W ^ (e + 1) := by
        rw [← map_sub, ← Finset.sum_sdiff (Finset.subset_union_left : S1 ⊆ S2), add_sub_cancel_right, map_sum]
        refine Ideal.sum_mem _ fun α hα => ?_
        have hα1 : α ∉ S1 := (Finset.mem_sdiff.1 hα).2
        have := hS (T.hD.xe.symm α) (fun hx => hα1 (by
          simp only [S1, Finset.mem_map_equiv]
          simpa using hx))
        simpa using this
      have h2' : T.φ s - T.φ (∑ α ∈ S2, v α) ∈ maximalIdeal W ^ (e + 1) := by
        rw [← map_sub]; exact hmap e (Ideal.mem_map_of_mem _ h2)
      refine ⟨c - (T.φ s - T.φ (∑ α ∈ S2, v α)) - (T.φ (∑ α ∈ S2, v α) - T.φ (∑ α ∈ S1, v α)),
        Ideal.sub_mem _ (Ideal.sub_mem _ hcm h2') hdiff, ?_⟩
      rw [heq, hsum1]
      congr 2
      ring
    haveI : IsDiscreteValuationRing W := ((GlobalTheory.LN.cDvr_iff W).1 T.cdvr).1
    choose c hc heq using step
    have hce : ∀ e, c e = c 0 := fun e => by
      have := (heq e).symm.trans (heq 0)
      have hu := (Units.isUnit ((val T.U.LG.rig (idW W) (cpt W) J') ^ k))
      rw [Units.val_pow_eq_pow_val] at hu
      have := hu.mul_right_cancel this
      apply add_left_cancel (a := T.φ s)
      apply stalkOf_injective (cpt W)
      exact this
    have h0 : c 0 = 0 := by
      have hm : c 0 ∈ ⨅ n : ℕ, maximalIdeal W ^ n := Submodule.mem_iInf _ |>.2 fun n => by
        rcases n with _ | n
        · simp
        · rw [← hce n]; exact hc n
      rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal W) (maximalIdeal.isMaximal W).ne_top, Submodule.mem_bot] at hm
    rw [heq 0, h0, add_zero]

end GlobalTheory.Mum
