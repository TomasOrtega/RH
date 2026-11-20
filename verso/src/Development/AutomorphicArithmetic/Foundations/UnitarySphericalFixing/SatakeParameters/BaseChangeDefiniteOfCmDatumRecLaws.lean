import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.UnitaryReadS

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.DefiniteBC
open PositivityTheory.Rg.BcN UpperTheory.BaseChangeIdentities UpperTheory.Zero.LLC

namespace UpperTheory.One.M.Ud

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

attribute [local instance] host_isCMField
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Take `⟨a, d, h, P, h1, h2, h3⟩` from `hMW n hn V hV hc`. Establish `had : a * d = n` using `by simpa [mul_comm] using h`. Establish `ha : 1 ≤ a` using `Nat.pos_of_mul_pos_right (had ▸ hn)`. Establish `hPG : ∀ w σ, P.IsLocComp w σ → Good (GlobalTheory.BCSupport.clsOf σ)` using `fun w σ hσ => by`. Take `⟨σ', hσ', hg⟩` from `hG w`.

Take `⟨-, σ₀, l, -, q⟩` from `h2 w σ' hσ'`. Establish `e : GlobalTheory.BCSupport.clsOf σ = GlobalTheory.BCSupport.clsOf σ₀` using `GlobalTheory.LocGL.IrrGL.of_eq_of.2 (GlobalTheory.CuspRep.LocUniq.isLocComp_unique P w σ σ₀ hσ l)`. Rewrite using `[e]`. Conclude with `GlobalTheory.DefiniteBCGood.good_of_isSpehQuot h σ₀ σ' (Nat.pos_of_mul_pos_left (had ▸ hn)) q hg`. Take `⟨π, c1, c2, c3⟩` from `hC a P ha h1 hPG`.

Use `⟨⟨a, π, d⟩, ha, Nat.pos_of_mul_pos_left (had ▸ hn), c1, had, fun w σ' hσ' => ?_, fun τ m' hm' => ?_⟩` and prove the remaining obligations. Take `⟨u, σ, l, u', q⟩` from `h2 w σ' hσ'`. Use `⟨u, ?_⟩` and prove the remaining obligations. Rewrite using `[hS w a d n h P σ σ' l u' q, ← c2 w σ l, spehLoc_eq]`. Take `⟨m, hm, rfl⟩` from `h3 τ m' hm'`.

Rewrite using `[c3 τ m hm]`.
-/
theorem part {rc : RecMap A} (hMW : DiscCsd H.E) (hS : RecSpeh rc) (hC : CuspReadG rc) {n : ℕ}
    (hn : 0 < n) {V : Submodule ℂ (Sm H.E n)} (hV : IsDiscrete V) (hc : CsdAsc V)
    (hG : ∀ w : PlE H, ∃ σ', IsLocCompGL V w σ' ∧ Good (GlobalTheory.BCSupport.clsOf σ')) :
    ∃ p : Part A.CG, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π ∧ p.a * p.d = n ∧
      (∀ w σ, IsLocCompGL V w σ → GlobalTheory.SmGL.IsUnitarisable σ.ρ ∧ rc w n σ = spehLoc N A p w) ∧
      ∀ τ m, HasInfCharGL V τ m → m = spehInf p.d (A.infG p.π τ) := by
  obtain ⟨a, d, h, P, h1, h2, h3⟩ := hMW n hn V hV hc
  have had : a * d = n := by simpa [mul_comm] using h
  have ha : 1 ≤ a := Nat.pos_of_mul_pos_right (had ▸ hn)
  have hPG : ∀ w σ, P.IsLocComp w σ → Good (GlobalTheory.BCSupport.clsOf σ) := fun w σ hσ => by
    obtain ⟨σ', hσ', hg⟩ := hG w
    obtain ⟨-, σ₀, l, -, q⟩ := h2 w σ' hσ'
    have e : GlobalTheory.BCSupport.clsOf σ = GlobalTheory.BCSupport.clsOf σ₀ :=
      GlobalTheory.LocGL.IrrGL.of_eq_of.2 (GlobalTheory.CuspRep.LocUniq.isLocComp_unique P w σ σ₀ hσ l)
    rw [e]
    exact GlobalTheory.DefiniteBCGood.good_of_isSpehQuot h σ₀ σ' (Nat.pos_of_mul_pos_left (had ▸ hn)) q hg
  obtain ⟨π, c1, c2, c3⟩ := hC a P ha h1 hPG
  refine ⟨⟨a, π, d⟩, ha, Nat.pos_of_mul_pos_left (had ▸ hn), c1, had, fun w σ' hσ' => ?_, fun τ m' hm' => ?_⟩
  · obtain ⟨u, σ, l, u', q⟩ := h2 w σ' hσ'
    refine ⟨u, ?_⟩
    rw [hS w a d n h P σ σ' l u' q, ← c2 w σ l, spehLoc_eq]
  · obtain ⟨m, hm, rfl⟩ := h3 τ m' hm'
    rw [c3 τ m hm]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

/- English proof (translation)
Take `⟨c, d, h, V, σ, m, bc⟩` from `hNT H.E (host_unramified H) n hn U hU`. Establish `hgood : ∀ i w, Good (GlobalTheory.BCSupport.clsOf (σ i w))` using `fun i w => by`. Distinguish the cases in `hw : IsSplitPl H w`. Establish `hc` using `bc.split w (isSplitAt_of_isSplitPl hw)`. Conclude with `GlobalTheory.BCSupport.good_of_good_locProd h w (σ · w) hc.1 (hGs w hw ⟨_, locProd h w (σ · w), GlobalTheory.SmGL.isSmooth_parInd _ _, hc.1⟩ hc) i`.

Take `⟨α, s, ϖ, q, e1, e2, e3⟩` from `hSat' w hw`. Conclude with `good_of_sph h w (σ · w) (bc.unram w (GlobalTheory.BcSpehCompare.isUnramU_of_hasSatAt e1 e2.2.1 e3)) i`. Use `choose p p1 p2 p3 p4 p5 p6 using fun i => Ud.part hMW hS hC (bc.pos i) (bc.discrete i) (bc.csd i) (fun w => ⟨σ i w, bc.loc i w, hgood i w⟩)`. Set `Q : ∀ w, LocIrr w n` to `fun w => { V := _ ρ := locProd h w (σ · w) smooth := GlobalTheory.SmGL.isSmooth_parInd _ _ irred := UpperTheory.Lit.Mix.multiProd_at (@UpperTheory.Lit.Mix.twoAt_charZero _ _ _ _ _ (charZero_of_injective_algebraMap (algebraMap H.E _).injective)) _ (fun i => (σ i w).smooth) (fun i …`. Establish `hloc : ∀ w, isoLoc N A (List.ofFn p) w = rc w n (Q w)` using `fun w => by`.

Rewrite using `[hP w c n d h (σ · w) (Q w) ⟨.refl _⟩]`. Simplify using `only [fun i => (p5 i w _ (bc.loc i w)).2]`. Rewrite using `[lpSumList, ← Function.comp_def (fun q => spehLoc N A q w) p, ← List.map_ofFn, List.foldr_map]`. Both sides reduce to the same expression. Establish `hinf : ∀ τ, isoInf N A (List.ofFn p) τ = ∑ i, m i τ` using `fun τ => by`.

Rewrite using `[isoInf_eq, List.map_ofFn, List.sum_ofFn]`. Conclude with `Finset.sum_congr rfl fun i _ => (p6 i τ _ (bc.inf i τ)).symm`. Use `⟨List.ofFn p, fun q hq => ?_, ?_, fun w hw => ⟨Q w, bc.split w (isSplitAt_of_isSplitPl hw), hloc w⟩, fun w α ⟨s, ϖ, q, e1, e2, e3⟩ => ?_, fun τ lam hl => ⟨List.nodup_ofFn.2 fun i j e => ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hq`. Conclude with `⟨p1 i, p2 i, p3 i⟩`.

Rewrite using `[rankIso, List.map_ofFn, List.sum_ofFn, ← h]`. Conclude with `Finset.sum_congr rfl fun i _ => p4 i`. Rewrite using `[hloc, ← ubc_eq_map_inv]`. Conclude with `hSat w n (Q w) _ (bc.inert w s ϖ q e1 e2 α e3)`. Use `GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin c) (m · τ) (bc.weight τ lam hl ▸ nodup_infOfWeight lam) i j (fun h0 => (bc.pos i).ne' ?_) ?_` and prove the remaining obligations.

Rewrite using `[← (bc.inf i τ).1]`. Conclude with `Multiset.card_eq_zero.2 h0`. Rewrite using `[p6 i τ _ (bc.inf i τ), p6 j τ _ (bc.inf j τ), e]`. Rewrite using `[hinf, bc.weight τ lam hl]`. Rewrite using `[hinf, bc.weight _ _ (hasWeightAt_conjugate hn hl), infOfWeight_dual]`.
-/
theorem parts {rc : RecMap A} (hNT : DefiniteN)
    (hMW : DiscCsd H.E)
    (hP : RecProd rc) (hS : RecSpeh rc) (hSat : RecSatake rc) (hC : CuspReadG rc)
    {n : ℕ} (hn : 1 ≤ n) {U : Submodule ℂ (UA H.E n → ℂ)} (hU : IsAutRepU U) (hGs : GlobalTheory.DefiniteBCGood.GoodSplitU U)
    (hSat' : ∀ w, ¬ IsSplitPl H w → ∃ α, IsSatAt U w α) :
    ∃ Pa : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧ rankIso N A Pa = n ∧
      (∀ w, IsSplitPl H w → ∃ σ : LocIrr w n,
        IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ isoLoc N A Pa w = rc w n σ) ∧
      (∀ w α, IsSatAt U w α → A.unr (isoLoc N A Pa w) ∧
        A.frobEig (isoLoc N A Pa w) = ubc n (Finset.univ.val.map fun i => (α i : ℂ))) ∧
      ∀ τ lam, HasWeightAt U τ lam → Pa.Nodup ∧ isoInf N A Pa τ = infOfWeight lam ∧
        isoInf N A Pa (ComplexEmbedding.conjugate τ) = (infOfWeight lam).map (fun z => -z) := by
  obtain ⟨c, d, h, V, σ, m, bc⟩ := hNT H.E (host_unramified H) n hn U hU
  have hgood : ∀ i w, Good (GlobalTheory.BCSupport.clsOf (σ i w)) := fun i w => by
    by_cases hw : IsSplitPl H w
    · have hc := bc.split w (isSplitAt_of_isSplitPl hw)
      exact GlobalTheory.BCSupport.good_of_good_locProd h w (σ · w) hc.1
        (hGs w hw ⟨_, locProd h w (σ · w), GlobalTheory.SmGL.isSmooth_parInd _ _, hc.1⟩ hc) i
    · obtain ⟨α, s, ϖ, q, e1, e2, e3⟩ := hSat' w hw
      exact good_of_sph h w (σ · w) (bc.unram w (GlobalTheory.BcSpehCompare.isUnramU_of_hasSatAt e1 e2.2.1 e3)) i
  choose p p1 p2 p3 p4 p5 p6 using fun i =>
    Ud.part hMW hS hC (bc.pos i) (bc.discrete i) (bc.csd i) (fun w => ⟨σ i w, bc.loc i w, hgood i w⟩)
  let Q : ∀ w, LocIrr w n := fun w =>
    { V := _
      ρ := locProd h w (σ · w)
      smooth := GlobalTheory.SmGL.isSmooth_parInd _ _
      irred := UpperTheory.Lit.Mix.multiProd_at (@UpperTheory.Lit.Mix.twoAt_charZero _ _ _ _ _ (charZero_of_injective_algebraMap (algebraMap H.E _).injective)) _ (fun i => (σ i w).smooth) (fun i => (σ i w).irred)
        fun i => (p5 i w _ (bc.loc i w)).1 }
  have hloc : ∀ w, isoLoc N A (List.ofFn p) w = rc w n (Q w) := fun w => by
    rw [hP w c n d h (σ · w) (Q w) ⟨.refl _⟩]
    simp only [fun i => (p5 i w _ (bc.loc i w)).2]
    rw [lpSumList, ← Function.comp_def (fun q => spehLoc N A q w) p, ← List.map_ofFn, List.foldr_map]
    rfl
  have hinf : ∀ τ, isoInf N A (List.ofFn p) τ = ∑ i, m i τ := fun τ => by
    rw [isoInf_eq, List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun i _ => (p6 i τ _ (bc.inf i τ)).symm
  refine ⟨List.ofFn p, fun q hq => ?_, ?_, fun w hw => ⟨Q w, bc.split w (isSplitAt_of_isSplitPl hw), hloc w⟩,
    fun w α ⟨s, ϖ, q, e1, e2, e3⟩ => ?_, fun τ lam hl => ⟨List.nodup_ofFn.2 fun i j e => ?_, ?_, ?_⟩⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hq
    exact ⟨p1 i, p2 i, p3 i⟩
  · rw [rankIso, List.map_ofFn, List.sum_ofFn, ← h]
    exact Finset.sum_congr rfl fun i _ => p4 i
  · rw [hloc, ← ubc_eq_map_inv]
    exact hSat w n (Q w) _ (bc.inert w s ϖ q e1 e2 α e3)
  · refine GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin c) (m · τ) (bc.weight τ lam hl ▸ nodup_infOfWeight lam) i j
      (fun h0 => (bc.pos i).ne' ?_) ?_
    · rw [← (bc.inf i τ).1]
      exact Multiset.card_eq_zero.2 h0
    · rw [p6 i τ _ (bc.inf i τ), p6 j τ _ (bc.inf j τ), e]
  · rw [hinf, bc.weight τ lam hl]
  · rw [hinf, bc.weight _ _ (hasWeightAt_conjugate hn hl), infOfWeight_dual]

/- English proof (translation)
Introduce `j h1 h2 π hπ`. Take `⟨U, u1, u2, u3, u4⟩` from `hU j h1 h2 π`. Take `⟨w₀, -, hw₀'⟩` from `PositivityTheory.Rg.BcB.F.Inert.ExistsNonSplitPlace.exists_not_isSplitAt (E := H.E) ∅ Set.finite_empty`. Establish `hw₀ : ¬ IsSplitPl H w₀` using `fun h => hw₀' (isSplitAt_of_isSplitPl h)`. Establish `hn : 1 ≤ R.nV`.

Use `R.rank_add_five_le` as an intermediate fact. Simplify using `only [Ranks.nV]`. Use linear arithmetic over natural numbers and integers. Take `⟨Pa, a1, a2, a3, a4, a5⟩` from `Ud.parts hNT hMW hP hS hSat hC hn u1 (u3 w₀ hw₀ (hπ w₀ hw₀)).1 fun w hw => (u3 w hw (hπ w hw)).2.imp fun _ h => h.1`. Use `⟨Pa, fun p hp => ⟨(a1 p hp).1, (a1 p hp).2.1⟩, fun p hp => (a1 p hp).2.2, ?_, a2, fun w hw => ?_, fun w hw => ?_, fun τ => ?_, fun τ _ => ?_⟩` and prove the remaining obligations.

Take `⟨lam, hl, -⟩` from `u4 H.φ₀`. Conclude with `(a5 _ lam hl).1`. Take `⟨σ, s1, s2⟩` from `a3 w hw`. Rewrite using `[s2, u2 w hw σ s1]`. Take `⟨α, s1, s2⟩` from `(u3 w hw (hπ w hw)).2`.

Rewrite using `[s2]`. Conclude with `a4 w α s1`. Take `⟨lam, hl, e⟩` from `u4 τ`. Rewrite using `[e, (a5 τ lam hl).2.1]`. Take `⟨lam, hl, e⟩` from `u4 τ`.

Rewrite using `[e, (a5 τ lam hl).2.2]`.
-/
theorem bcAt (B : NBC A) (rc : RecMap A) (hNT : DefiniteN)
    (hMW : DiscCsd H.E)
    (hP : RecProd rc) (hS : RecSpeh rc) (hSat : RecSatake rc) (hC : CuspReadG rc) (hU : UnitaryReadS B rc) :
    GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness.BaseChangeDefinite_at B := by
  intro j h1 h2 π hπ
  obtain ⟨U, u1, u2, u3, u4⟩ := hU j h1 h2 π
  obtain ⟨w₀, -, hw₀'⟩ := PositivityTheory.Rg.BcB.F.Inert.ExistsNonSplitPlace.exists_not_isSplitAt (E := H.E) ∅ Set.finite_empty
  have hw₀ : ¬ IsSplitPl H w₀ := fun h => hw₀' (isSplitAt_of_isSplitPl h)
  have hn : 1 ≤ R.nV := by
    have := R.rank_add_five_le
    simp only [Ranks.nV]
    omega
  obtain ⟨Pa, a1, a2, a3, a4, a5⟩ := Ud.parts hNT hMW hP hS hSat hC hn u1 (u3 w₀ hw₀ (hπ w₀ hw₀)).1
    fun w hw => (u3 w hw (hπ w hw)).2.imp fun _ h => h.1
  refine ⟨Pa, fun p hp => ⟨(a1 p hp).1, (a1 p hp).2.1⟩, fun p hp => (a1 p hp).2.2, ?_, a2, fun w hw => ?_,
    fun w hw => ?_, fun τ => ?_, fun τ _ => ?_⟩
  · obtain ⟨lam, hl, -⟩ := u4 H.φ₀
    exact (a5 _ lam hl).1
  · obtain ⟨σ, s1, s2⟩ := a3 w hw
    rw [s2, u2 w hw σ s1]
  · obtain ⟨α, s1, s2⟩ := (u3 w hw (hπ w hw)).2
    rw [s2]
    exact a4 w α s1
  · obtain ⟨lam, hl, e⟩ := u4 τ
    rw [e, (a5 τ lam hl).2.1]
  · obtain ⟨lam, hl, e⟩ := u4 τ
    rw [e, (a5 τ lam hl).2.2]

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions

/- English proof (translation)
Introduce `D rc hNT hMW hP hS hSat hC hU _ _ j h1 h2 _ _ π hπ`. Take `⟨Pa, hPa⟩` from `Ud.bcAt D.nbc rc hNT hMW hP hS hSat hC hU j h1 h2 π hπ`. Conclude with `⟨Pa, GlobalTheory.DefiniteBCFrozen.isBC_of_isBaseChange hPa⟩`.
-/
theorem baseChangeDefinite_of_cmDatum_recLaws : ∀ (D : D7) (rc : RecMap D.naut), DefiniteN →
    DiscCsd D.host.E → RecProd rc → RecSpeh rc →
    RecSatake rc → CuspReadG rc → UnitaryReadS D.nbc rc → SphericalInertData.Conclusion1 D := by
  intro D rc hNT hMW hP hS hSat hC hU _ _ j h1 h2 _ _ π hπ
  obtain ⟨Pa, hPa⟩ := Ud.bcAt D.nbc rc hNT hMW hP hS hSat hC hU j h1 h2 π hπ
  exact ⟨Pa, GlobalTheory.DefiniteBCFrozen.isBC_of_isBaseChange hPa⟩

end UpperTheory.One.M.Ud

end
