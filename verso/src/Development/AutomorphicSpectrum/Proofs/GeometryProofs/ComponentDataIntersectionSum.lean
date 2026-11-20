import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsChartBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueLatOfChartBundle
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BigBlock

/- English proof (translation)
Establish `h` using `alternating_map_sum_smul_eq_det_smul (exteriorPower.ιMulti Ω r (M := Q)) T.transpose w`. Simplify `h` using `[Matrix.det_transpose]`.
-/
theorem iotaMulti_comb {Ω Q : Type} [Field Ω] [AddCommGroup Q] [Module Ω Q] {r : ℕ} (T : Matrix (Fin r) (Fin r) Ω)
    (w : Fin r → Q) :
    exteriorPower.ιMulti Ω r (fun k => ∑ k', T k' k • w k') = T.det • exteriorPower.ιMulti Ω r w := by
  have h := alternating_map_sum_smul_eq_det_smul (exteriorPower.ιMulti Ω r (M := Q)) T.transpose w
  simpa [Matrix.det_transpose] using h

/- English proof (translation)
Establish `h1 : t ∈ Submodule.span (regAt ξ p) {t'}` using `h ▸ Submodule.mem_span_singleton_self t`. Establish `h2 : t' ∈ Submodule.span (regAt ξ p) {t}` using `h ▸ Submodule.mem_span_singleton_self t'`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.1 h1`. Take `⟨a', ha'⟩` from `Submodule.mem_span_singleton.1 h2`. Establish `ha1 : (a : Ω) * t' = t` using `ha`.

Establish `ha2 : (a' : Ω) * t = t'` using `ha'`. Use `⟨div_ne_zero ht ht', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← ha1, mul_div_cancel_right₀ _ ht']`. Conclude with `a.2`. Rewrite using `[inv_div, ← ha2, mul_div_cancel_right₀ _ ht]`.

Conclude with `a'.2`.
-/
theorem unitAt_div_of_span_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}
    {t t' : Ω} (ht : t ≠ 0) (ht' : t' ≠ 0)
    (h : Submodule.span (regAt ξ p) {t} = Submodule.span (regAt ξ p) {t'}) : unitAt ξ p (t / t') := by
  have h1 : t ∈ Submodule.span (regAt ξ p) {t'} := h ▸ Submodule.mem_span_singleton_self t
  have h2 : t' ∈ Submodule.span (regAt ξ p) {t} := h ▸ Submodule.mem_span_singleton_self t'
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨a', ha'⟩ := Submodule.mem_span_singleton.1 h2
  have ha1 : (a : Ω) * t' = t := ha
  have ha2 : (a' : Ω) * t = t' := ha'
  refine ⟨div_ne_zero ht ht', ?_, ?_⟩
  · rw [← ha1, mul_div_cancel_right₀ _ ht']
    exact a.2
  · rw [inv_div, ← ha2, mul_div_cancel_right₀ _ ht]
    exact a'.2

/- English proof (translation)
Use `⟨Finset.univ.inf U, ?_, fun i => Finset.inf_le (Finset.mem_univ i)⟩` and prove the remaining obligations. Establish `: ∀ s : Finset I, x ∈ s.inf U` using `fun s => by`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s _ ih`.

Rewrite using `[Finset.inf_insert]`. Conclude with `⟨h a, ih⟩`. Conclude with `this _`.
-/
theorem exists_open_le {X : Scheme.{0}} {I : Type} [Fintype I] (U : I → X.Opens) {x : X} (h : ∀ i, x ∈ U i) :
    ∃ V : X.Opens, x ∈ V ∧ ∀ i, V ≤ U i := by
  classical
  refine ⟨Finset.univ.inf U, ?_, fun i => Finset.inf_le (Finset.mem_univ i)⟩
  have : ∀ s : Finset I, x ∈ s.inf U := fun s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s _ ih =>
      rw [Finset.inf_insert]
      exact ⟨h a, ih⟩
  exact this _

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨l₀, hl₀⟩ : ∃ l, f l ≠ 0 := by`. Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, not_not] at h`. Simplify using `[h] at hsum`. Use `⟨fun l => if f l = 0 then f l₀ else f l, fun l => if f l = 0 then 0 else g l, fun l => ?_, fun l => ?_, ?_, fun l => ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `dsimp only; split_ifs <;> exact hf _`. Simplify using `only`. Use `split_ifs`. Conclude with `zero_mem _`. Conclude with `hg l`.

Rewrite using `[← hsum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : f l = 0 <;> simp [h]`. Simplify using `only`. Use `split_ifs with h`.

Conclude with `hP _ hl₀`. Conclude with `hP _ h`.
-/
theorem exists_nonzero_cover {Ω : Type} [Field Ω] (R : Subring Ω) (Pr : Ω → Prop) {k : ℕ} (f g : Fin k → Ω)
    (hf : ∀ l, f l ∈ R) (hg : ∀ l, g l ∈ R) (hsum : ∑ l, g l * f l = 1) (hP : ∀ l, f l ≠ 0 → Pr (f l)) :
    ∃ (f' g' : Fin k → Ω), (∀ l, f' l ∈ R) ∧ (∀ l, g' l ∈ R) ∧ ∑ l, g' l * f' l = 1 ∧ ∀ l, Pr (f' l) := by
  classical
  obtain ⟨l₀, hl₀⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at hsum
  refine ⟨fun l => if f l = 0 then f l₀ else f l, fun l => if f l = 0 then 0 else g l, fun l => ?_, fun l => ?_, ?_,
    fun l => ?_⟩
  · dsimp only; split_ifs <;> exact hf _
  · dsimp only; split_ifs
    · exact zero_mem _
    · exact hg l
  · rw [← hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : f l = 0 <;> simp [h]
  · dsimp only; split_ifs with h
    · exact hP _ hl₀
    · exact hP _ h

end GlobalTheory.CompanionTheory.Ar.BigBlock

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BigBlock

/- English proof (translation)
Take `⟨n, rfl | rfl⟩` from `n.eq_nat_or_neg`. Simplify using `using pow_mem h.2.1 n`. Simplify using `using pow_mem h.2.2 n`.
-/
theorem zpow_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} {a : Ω}
    (h : unitAt ξ p a) (n : ℤ) : a ^ n ∈ regAt ξ p := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using pow_mem h.2.1 n
  · simpa using pow_mem h.2.2 n

/- English proof (translation)
Introduce `X Ω _ ξ I _ Λ a p t ht`. Use `⟨Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (ht i).1, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨s', hs', rfl⟩`. Establish `hu : ∀ i, unitAt ξ p (s' i / t i)` using `fun i => unitAt_div_of_span_eq (hs' i).1 (ht i).1 ((hs' i).2.symm.trans (ht i).2)`.

Establish `hreg : ∏ i, (s' i / t i) ^ a i ∈ regAt ξ p` using `prod_mem fun i _ => zpow_mem_regAt (hu i) (a i)`. Use `Submodule.mem_span_singleton.2 ⟨⟨_, hreg⟩, ?_⟩` and prove the remaining obligations. Use `show (∏ i, (s' i / t i) ^ a i) * ∏ i, t i ^ a i = ∏ i, s' i ^ a i`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← mul_zpow, div_mul_cancel₀ _ (ht i).1]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ rfl`. Conclude with `Submodule.subset_span ⟨t, ht, rfl⟩`.
-/
theorem tens_isGenAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (t : I → Ω), (∀ i, (Λ i).IsGenAt p (t i)) → (Lat.tens Λ a).IsGenAt p (∏ i, t i ^ a i) := by
  intro X Ω _ ξ I _ Λ a p t ht
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (ht i).1, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro x ⟨s', hs', rfl⟩
    have hu : ∀ i, unitAt ξ p (s' i / t i) := fun i =>
      unitAt_div_of_span_eq (hs' i).1 (ht i).1 ((hs' i).2.symm.trans (ht i).2)
    have hreg : ∏ i, (s' i / t i) ^ a i ∈ regAt ξ p := prod_mem fun i _ => zpow_mem_regAt (hu i) (a i)
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hreg⟩, ?_⟩
    show (∏ i, (s' i / t i) ^ a i) * ∏ i, t i ^ a i = ∏ i, s' i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_zpow, div_mul_cancel₀ _ (ht i).1]
  · refine Submodule.span_le.2 ?_
    rintro _ rfl
    exact Submodule.subset_span ⟨t, ht, rfl⟩

/- English proof (translation)
Introduce `X Ω _ ξ P _ _ L r s b T p hs hb hT`. Establish `hdet : T.det ≠ 0`. Introduce `h0`. Take `⟨v, hv, hTv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Use `hv (funext fun k => Fintype.linearIndependent_iff.1 hb.1 v ?_ k)` and prove the remaining obligations.

Establish `h1 : ∑ k, v k • b k = ∑ a, (T.mulVec v a) • s a`. Repeatedly rewrite using `[hT, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]`. Rewrite using `[h1, hTv]`.

Simplify using the standard rewrite rules. Use `⟨hdet, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩` and prove the remaining obligations. Introduce and unpack `t ⟨b', T', hb', hT', rfl⟩`. Establish `hex : ∀ k, ∃ A : Fin r → regAt ξ p, ∑ k', A k' • b k' = b' k` using `fun k => by`. Establish `h` using `ChartTie.frame_mem hb' k`.

Rewrite `h` using `[hb.2]`. Conclude with `(Submodule.mem_span_range_iff_exists_fun _).1 h`. Use `choose A hA using hex`. Establish `hcoef : ∀ k a, T' a k = ∑ m, T a m * (A k m : Ω)`. Introduce `k`.

Establish `h` using `Fintype.linearIndependent_iff.1 hs (fun a => T' a k - ∑ m, T a m * (A k m : Ω)) (by`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[← hT' k, ← hA k, sub_eq_zero]`. Establish `e : ∀ m, A k m • b m = (A k m : Ω) • b m` using `fun _ => rfl`. Repeatedly rewrite using `[e, hT, Finset.smul_sum, smul_smul, Finset.sum_smul]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m _ => by rw [mul_comm])`. Conclude with `fun a => sub_eq_zero.1 (h a)`. Set `M : Matrix (Fin r) (Fin r) (regAt ξ p)` to `Matrix.of fun m k => A k m`. Establish `hTT : T' = T * (regAt ξ p).subtype.mapMatrix M`.

Use extensionality with `a k`. Rewrite using `[hcoef, Matrix.mul_apply]`. Both sides reduce to the same expression. Use `Submodule.mem_span_singleton.2 ⟨M.det, ?_⟩` and prove the remaining obligations. Use `show ((M.det : regAt ξ p) : Ω) * T.det = T'.det`.

Rewrite using `[hTT, Matrix.det_mul, ← RingHom.map_det, mul_comm]`. Both sides reduce to the same expression. Introduce and unpack `_ rfl`. Conclude with `Submodule.subset_span ⟨b, T, hb, hT, rfl⟩`.
-/
theorem detLat_isGenAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (P : Type) [AddCommGroup P] [Module Ω P] (L : Lat ξ P) (r : ℕ) (s b : Fin r → P) (T : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω s → L.IsFrameAt b p → (∀ k, b k = ∑ k', T k' k • s k') → (Cusp.detLat L s).IsGenAt p T.det := by
  intro X Ω _ ξ P _ _ L r s b T p hs hb hT
  have hdet : T.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hTv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    refine hv (funext fun k => Fintype.linearIndependent_iff.1 hb.1 v ?_ k)
    have h1 : ∑ k, v k • b k = ∑ a, (T.mulVec v a) • s a := by
      simp_rw [hT, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]
    rw [h1, hTv]
    simp
  refine ⟨hdet, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩
  · rintro t ⟨b', T', hb', hT', rfl⟩
    have hex : ∀ k, ∃ A : Fin r → regAt ξ p, ∑ k', A k' • b k' = b' k := fun k => by
      have h := ChartTie.frame_mem hb' k
      rw [hb.2] at h
      exact (Submodule.mem_span_range_iff_exists_fun _).1 h
    choose A hA using hex
    have hcoef : ∀ k a, T' a k = ∑ m, T a m * (A k m : Ω) := by
      intro k
      have h := Fintype.linearIndependent_iff.1 hs (fun a => T' a k - ∑ m, T a m * (A k m : Ω)) (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hT' k, ← hA k, sub_eq_zero]
        have e : ∀ m, A k m • b m = (A k m : Ω) • b m := fun _ => rfl
        simp_rw [e, hT, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m _ => by rw [mul_comm])
      exact fun a => sub_eq_zero.1 (h a)
    let M : Matrix (Fin r) (Fin r) (regAt ξ p) := Matrix.of fun m k => A k m
    have hTT : T' = T * (regAt ξ p).subtype.mapMatrix M := by
      ext a k
      rw [hcoef, Matrix.mul_apply]
      rfl
    refine Submodule.mem_span_singleton.2 ⟨M.det, ?_⟩
    show ((M.det : regAt ξ p) : Ω) * T.det = T'.det
    rw [hTT, Matrix.det_mul, ← RingHom.map_det, mul_comm]
    rfl
  · rintro _ rfl
    exact Submodule.subset_span ⟨b, T, hb, hT, rfl⟩

/- English proof (translation)
Introduce `X Ω _ ξ P Wv _ _ _ _ i A B Va Vb N j hj hinj hrange hA hB hL p`. Take `⟨U1, hp1, b1, hs1, hf1⟩` from `hA p trivial`. Take `⟨U2, hp2, b2, hs2, hf2⟩` from `hB p trivial`. Take `⟨U3, hp3, b3, hs3, hf3⟩` from `hL p trivial`. Establish `hli3` using `(hf3 p trivial hp3).1`.

Set `B3` to `Module.Basis.mk hli3 hs3.ge`. Establish `: Module.Finite Ω Wv` using `Module.Finite.of_basis B3`. Establish `hfin : Module.finrank Ω Wv = N` using `by simpa using Module.finrank_eq_card_basis B3`. Set `v : Fin N → P` to `fun k => if h : (k : ℕ) < j then b1 ⟨k, h⟩ else b2 ⟨k - j, by have := k.2; omega⟩`. Establish `hvh : ∀ a, v (headIdx hj a) = b1 a` using `fun a => by`.

Establish `h : ((headIdx hj a : Fin N) : ℕ) < j` using `a.2`. Simplify using `only [v, dif_pos h]`. Both sides reduce to the same expression. Establish `hvt : ∀ a, v (tailIdx hj a) = b2 a` using `fun a => by`. Establish `h : ¬ ((tailIdx hj a : Fin N) : ℕ) < j` using `by simp [tailIdx]`.

Simplify using `only [v, dif_neg h]`. Use `congr 1`. Use `ext`. Simplify using `[tailIdx]`. Establish `hcase : ∀ k : Fin N, (∃ a, k = headIdx hj a) ∨ ∃ a, k = tailIdx hj a` using `fun k => by`.

Distinguish the cases in `h : (k : ℕ) < j`. Conclude with `Or.inl ⟨⟨k, h⟩, by ext; rfl⟩`. Conclude with `Or.inr ⟨⟨k - j, by have := k.2; omega⟩, by ext; simp [tailIdx]; omega⟩`. Establish `hspanv : Submodule.span Ω (Set.range v) = Va ⊔ Vb`. Use `le_antisymm (Submodule.span_le.2 ?_) (sup_le ?_ ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, rfl⟩`. Break down `hcase k with ⟨a, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Rewrite using `[hvh]`. Conclude with `Submodule.mem_sup_left (hs1 ▸ Submodule.subset_span ⟨a, rfl⟩)`. Rewrite using `[hvt]`.

Conclude with `Submodule.mem_sup_right (hs2 ▸ Submodule.subset_span ⟨a, rfl⟩)`. Rewrite using `[← hs1]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `Submodule.subset_span ⟨headIdx hj a, hvh a⟩`.

Rewrite using `[← hs2]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `Submodule.subset_span ⟨tailIdx hj a, hvt a⟩`. Establish `hrank : Module.finrank Ω (Submodule.span Ω (Set.range v)) = N`.

Rewrite using `[hspanv, ← hrange, LinearMap.finrank_range_of_inj hinj, hfin]`. Establish `hliv : LinearIndependent Ω v` using `linearIndependent_iff_card_eq_finrank_span.2 (by simpa [Set.finrank] using hrank.symm)`. Establish `hpre : ∀ k, ∃ w, i w = v k` using `fun k => by`. Establish `h : v k ∈ LinearMap.range i`. Rewrite using `[hrange, ← hspanv]`.

Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Conclude with `h`. Use `choose b hb using hpre`. Establish `hlib : LinearIndependent Ω b` using `LinearIndependent.of_comp i (by`. Establish `: (i ∘ b) = v` using `funext hb`.

Rewrite using `[show (⇑i ∘ b) = v from this]`. Conclude with `hliv)`. Establish `hspanb : Submodule.span Ω (Set.range b) = ⊤` using `hlib.span_eq_top_of_card_eq_finrank' (by simp [hfin])`. Use `⟨U1 ⊓ U2, ⟨hp1, hp2⟩, b, hspanb, ?_, fun a => ?_, fun q hq => ?_⟩` and prove the remaining obligations. Establish `hm : (Submodule.span Ω (Set.range (b ∘ headIdx hj))).map i = Va`.

Rewrite using `[Submodule.map_span, ← Set.range_comp, ← hs1]`. Use `congr 2`. Use function extensionality and compare the values at `a`. Simplify using `[hb, hvh]`. Rewrite using `[← hm, Submodule.comap_map_eq_of_injective hinj]`.

Rewrite using `[hb, hvt, ← hs2]`. Conclude with `Submodule.subset_span ⟨a, rfl⟩`. Establish `e1` using `(hf1 q trivial hq.1).2`. Establish `e2` using `(hf2 q trivial hq.2).2`. Establish `hsum : A q ⊔ B q = (Submodule.span (regAt ξ q) (Set.range b)).map (i.restrictScalars (regAt ξ q))`.

Rewrite using `[Submodule.map_span, e1, e2]`. Use `le_antisymm (sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `Submodule.subset_span ⟨b (headIdx hj a), ⟨_, rfl⟩, by simp [hb, hvh]⟩`. Introduce and unpack `_ ⟨a, rfl⟩`.

Conclude with `Submodule.subset_span ⟨b (tailIdx hj a), ⟨_, rfl⟩, by simp [hb, hvt]⟩`. Introduce and unpack `_ ⟨_, ⟨k, rfl⟩, rfl⟩ show i (b k) ∈ _`. Rewrite using `[hb]`. Break down `hcase k with ⟨a, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Rewrite using `[hvh]`.

Conclude with `Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)`. Rewrite using `[hvt]`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩)`. Use `⟨⟨hlib, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show (A q ⊔ B q).comap (i.restrictScalars (regAt ξ q)) = _`.

Rewrite using `[hsum]`. Conclude with `Submodule.comap_map_eq_of_injective (show Function.Injective (i.restrictScalars (regAt ξ q)) from hinj) _`. Establish `: (fun a => i (b (tailIdx hj a))) = b2` using `funext fun a => by rw [hb, hvt]`. Rewrite using `[this]`. Conclude with `(hf2 q trivial hq.2).1`.

Establish `: (fun a => i (b (tailIdx hj a))) = b2` using `funext fun a => by rw [hb, hvt]`. Rewrite using `[this]`. Conclude with `e2`.
-/
theorem exists_block_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (P Wv : Type) [AddCommGroup P] [Module Ω P] [AddCommGroup Wv] [Module Ω Wv] (i : Wv →ₗ[Ω] P) (A B : Lat ξ P) (Va Vb : Submodule Ω P) (N j : ℕ) (hj : j ≤ N), Function.Injective i → LinearMap.range i = Va ⊔ Vb → A.IsVB j Va → B.IsVB (N - j) Vb → (Lat.comap (fun p => A p ⊔ B p) i).IsVB N ⊤ → ∀ p : Cpt ξ, ∃ U : X.Opens, p.1 ∈ U ∧ ∃ b : Fin N → Wv, Submodule.span Ω (Set.range b) = ⊤ ∧ Submodule.span Ω (Set.range (b ∘ headIdx hj)) = Va.comap i ∧ (∀ a, i (b (tailIdx hj a)) ∈ Vb) ∧ ∀ q : Cpt ξ, q.1 ∈ U → (Lat.comap (fun p => A p ⊔ B p) i).IsFrameAt b q ∧ B.IsFrameAt (fun a => i (b (tailIdx hj a))) q := by
  intro X Ω _ ξ P Wv _ _ _ _ i A B Va Vb N j hj hinj hrange hA hB hL p
  obtain ⟨U1, hp1, b1, hs1, hf1⟩ := hA p trivial
  obtain ⟨U2, hp2, b2, hs2, hf2⟩ := hB p trivial
  obtain ⟨U3, hp3, b3, hs3, hf3⟩ := hL p trivial
  have hli3 := (hf3 p trivial hp3).1
  let B3 := Module.Basis.mk hli3 hs3.ge
  have : Module.Finite Ω Wv := Module.Finite.of_basis B3
  have hfin : Module.finrank Ω Wv = N := by simpa using Module.finrank_eq_card_basis B3
  let v : Fin N → P := fun k => if h : (k : ℕ) < j then b1 ⟨k, h⟩ else b2 ⟨k - j, by have := k.2; omega⟩
  have hvh : ∀ a, v (headIdx hj a) = b1 a := fun a => by
    have h : ((headIdx hj a : Fin N) : ℕ) < j := a.2
    simp only [v, dif_pos h]
    rfl
  have hvt : ∀ a, v (tailIdx hj a) = b2 a := fun a => by
    have h : ¬ ((tailIdx hj a : Fin N) : ℕ) < j := by simp [tailIdx]
    simp only [v, dif_neg h]
    congr 1
    ext
    simp [tailIdx]
  have hcase : ∀ k : Fin N, (∃ a, k = headIdx hj a) ∨ ∃ a, k = tailIdx hj a := fun k => by
    by_cases h : (k : ℕ) < j
    · exact Or.inl ⟨⟨k, h⟩, by ext; rfl⟩
    · exact Or.inr ⟨⟨k - j, by have := k.2; omega⟩, by ext; simp [tailIdx]; omega⟩
  have hspanv : Submodule.span Ω (Set.range v) = Va ⊔ Vb := by
    refine le_antisymm (Submodule.span_le.2 ?_) (sup_le ?_ ?_)
    · rintro _ ⟨k, rfl⟩
      rcases hcase k with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [hvh]
        exact Submodule.mem_sup_left (hs1 ▸ Submodule.subset_span ⟨a, rfl⟩)
      · rw [hvt]
        exact Submodule.mem_sup_right (hs2 ▸ Submodule.subset_span ⟨a, rfl⟩)
    · rw [← hs1]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨headIdx hj a, hvh a⟩
    · rw [← hs2]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨tailIdx hj a, hvt a⟩
  have hrank : Module.finrank Ω (Submodule.span Ω (Set.range v)) = N := by
    rw [hspanv, ← hrange, LinearMap.finrank_range_of_inj hinj, hfin]
  have hliv : LinearIndependent Ω v :=
    linearIndependent_iff_card_eq_finrank_span.2 (by simpa [Set.finrank] using hrank.symm)
  have hpre : ∀ k, ∃ w, i w = v k := fun k => by
    have h : v k ∈ LinearMap.range i := by
      rw [hrange, ← hspanv]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact h
  choose b hb using hpre
  have hlib : LinearIndependent Ω b := LinearIndependent.of_comp i (by
    have : (i ∘ b) = v := funext hb
    rw [show (⇑i ∘ b) = v from this]
    exact hliv)
  have hspanb : Submodule.span Ω (Set.range b) = ⊤ :=
    hlib.span_eq_top_of_card_eq_finrank' (by simp [hfin])
  refine ⟨U1 ⊓ U2, ⟨hp1, hp2⟩, b, hspanb, ?_, fun a => ?_, fun q hq => ?_⟩
  · have hm : (Submodule.span Ω (Set.range (b ∘ headIdx hj))).map i = Va := by
      rw [Submodule.map_span, ← Set.range_comp, ← hs1]
      congr 2
      funext a
      simp [hb, hvh]
    rw [← hm, Submodule.comap_map_eq_of_injective hinj]
  · rw [hb, hvt, ← hs2]
    exact Submodule.subset_span ⟨a, rfl⟩
  · have e1 := (hf1 q trivial hq.1).2
    have e2 := (hf2 q trivial hq.2).2
    have hsum : A q ⊔ B q =
        (Submodule.span (regAt ξ q) (Set.range b)).map (i.restrictScalars (regAt ξ q)) := by
      rw [Submodule.map_span, e1, e2]
      refine le_antisymm (sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)) (Submodule.span_le.2 ?_)
      · rintro _ ⟨a, rfl⟩
        exact Submodule.subset_span ⟨b (headIdx hj a), ⟨_, rfl⟩, by simp [hb, hvh]⟩
      · rintro _ ⟨a, rfl⟩
        exact Submodule.subset_span ⟨b (tailIdx hj a), ⟨_, rfl⟩, by simp [hb, hvt]⟩
      · rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
        show i (b k) ∈ _
        rw [hb]
        rcases hcase k with ⟨a, rfl⟩ | ⟨a, rfl⟩
        · rw [hvh]
          exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
        · rw [hvt]
          exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩)
    refine ⟨⟨hlib, ?_⟩, ?_, ?_⟩
    · show (A q ⊔ B q).comap (i.restrictScalars (regAt ξ q)) = _
      rw [hsum]
      exact Submodule.comap_map_eq_of_injective (show Function.Injective (i.restrictScalars (regAt ξ q)) from hinj) _
    · have : (fun a => i (b (tailIdx hj a))) = b2 := funext fun a => by rw [hb, hvt]
      rw [this]
      exact (hf2 q trivial hq.2).1
    · have : (fun a => i (b (tailIdx hj a))) = b2 := funext fun a => by rw [hb, hvt]
      rw [this]
      exact e2

end GlobalTheory.CompanionTheory.Ar.BigBlock

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BigBlock

open GlobalTheory.CompanionTheory.Ar.ChartTie in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc S₀ 𝔐 bg sm i s aMu e₀ hinj hrange hne hbg hsm hvb hch hsli hsspan hdeg`. Establish `hT : CoordTie ℤ 𝔐.ξ (segreCoord Dc.y)` using `𝔐.tie`. Establish `hVB : ∀ t, (𝔐.V t).IsVB (labelRk D t) (𝔐.Vgen t)` using `𝔐.vb`. Establish `hj` using `Dc.j_le_N`. Establish `hpre : ∀ τ a, ∃ w, i τ w = s τ a` using `fun τ a => by`.

Establish `h : s τ a ∈ LinearMap.range (i τ)`. Rewrite using `[hrange τ]`. Conclude with `Submodule.mem_sup_right (hsspan τ ▸ Submodule.subset_span ⟨a, rfl⟩)`. Conclude with `h`. Use `choose w hw using hpre`.

Establish `he₀ : e₀ ≠ 0` using `hdeg.1`. Set `F : ∀ τ, Submodule Ω (W τ)` to `fun τ => (𝔐.Vgen (bg τ)).comap (i τ)`. Set `Pw : PiTensorProduct Ω (fun τ => ⋀[Ω]^(Dc.N - Dc.j) (W τ ⧸ F τ))` to `PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω (Dc.N - Dc.j) fun a => (F τ).mkQ (w τ a)`. Use `⟨⟨F, aMu, e₀⁻¹ • Pw, ?_⟩, fun _ => rfl⟩` and prove the remaining obligations. Introduce `c hc`.

Set `Q : 𝔐.X.Opens → Prop` to `fun V => ∃ b : ∀ τ, Fin Dc.N → W τ, (∀ τ, Submodule.span Ω (Set.range (b τ)) = ⊤) ∧ (∀ τ, Submodule.span Ω (Set.range (b τ ∘ headIdx hj)) = F τ) ∧ (∀ τ a, i τ (b τ (tailIdx hj a)) ∈ 𝔐.Vgen (sm τ)) ∧ ∀ τ (q : Cpt 𝔐.ξ), q.1 ∈ V → (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i …`. Establish `hQ : ∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord Dc.y) c p → ∃ V : 𝔐.X.Opens, p.1 ∈ V ∧ Q V`. Introduce `p _`. Establish `hloc` using `fun τ => exists_block_frame 𝔐.X Ω 𝔐.ξ 𝔐.Li (W τ) (i τ) (𝔐.V (bg τ)) (𝔐.V (sm τ)) (𝔐.Vgen (bg τ)) (𝔐.Vgen (sm τ)) Dc.N Dc.j hj (hinj τ) (hrange τ) (hbg τ ▸ hVB (bg τ)) (hsm τ ▸ hVB (sm τ)) (hvb τ) p`. Use `choose U hpU b hb1 hb2 hb3 hb4 using hloc`.

Take `⟨V, hpV, hVU⟩` from `exists_open_le U hpU`. Conclude with `⟨V, hpV, b, hb1, hb2, hb3, fun τ q hq => hb4 τ q (hVU τ hq)⟩`. Take `⟨k, f, g, hf, hg, hsum, hl⟩` from `exists_cover hT hc Q hQ`. Set `p₀ : Cpt 𝔐.ξ` to `⟨genPt 𝔐.ξ, specializes_rfl⟩`. Establish `hreg₀ : ∀ a : Ω, a ∈ regAt 𝔐.ξ p₀` using `TieVB.regAt_genPt hT.gen`.

Establish `hp₀ : InChart 𝔐.ξ (segreCoord Dc.y) c p₀` using `⟨hc, fun c' => hreg₀ _⟩`. Establish `key : ∀ l, f l ≠ 0 → ∃ b : ∀ τ, Fin Dc.N → W τ, (∀ τ, IsAdaptedFrame Dc.y (Dc.W τ) (F τ) hj c (f l) (b τ)) ∧ ∃ u : Ω, IsUnitOn Dc.y c (f l) u ∧ e₀⁻¹ • Pw = (u * chartMono Dc.y c aMu) • PiTensorProduct.tprod Ω fun τ => quotWedge (F τ) hj (b τ)`. Introduce `l hfl`. Take `⟨V, ⟨b, hspan, hhead, hmem, hfr⟩, hV⟩` from `hl l`. Use `⟨b, fun τ => ⟨(GlobalTheory.T.segre_chart_bundle 𝔐.X Ω 𝔐.ξ K J Dc.y (W τ) Dc.N (Dc.W τ) _ hT (hvb τ) (hch τ) c (f l) (b τ) hc (hf l) hfl).2 fun p hp hu => (hfr τ p (hV p hp hu)).1, hspan τ, hhead τ⟩, ?_⟩` and prove the remaining obligations.

Establish `hex : ∀ τ, ∃ T : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω, ∀ a, i τ (b τ (tailIdx hj a)) = ∑ a', T a' a • s τ a'` using `fun τ => by`. Establish `h : ∀ a, ∃ v : Fin (Dc.N - Dc.j) → Ω, ∑ a', v a' • s τ a' = i τ (b τ (tailIdx hj a))` using `fun a => (Submodule.mem_span_range_iff_exists_fun Ω).1 (by rw [hsspan τ]; exact hmem τ a)`. Use `choose v hv using h`. Conclude with `⟨Matrix.of fun a' a => v a a', fun a => (hv a).symm⟩`. Use `choose T hTs using hex`.

Establish `hbw : ∀ τ a, b τ (tailIdx hj a) = ∑ a', T τ a' a • w τ a'` using `fun τ a => hinj τ (by`. Rewrite using `[hTs, map_sum]`. Conclude with `Finset.sum_congr rfl fun a' _ => by rw [map_smul, hw])`. Establish `hq : ∀ τ, quotWedge (F τ) hj (b τ) = (T τ).det • exteriorPower.ιMulti Ω (Dc.N - Dc.j) fun a => (F τ).mkQ (w τ a)` using `fun τ => by`. Rewrite using `[← iotaMulti_comb]`.

Unfold `quotWedge`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[hbw, map_sum]`. Conclude with `Finset.sum_congr rfl fun a' _ => by rw [map_smul]`.

Establish `htp : (PiTensorProduct.tprod Ω fun τ => quotWedge (F τ) hj (b τ)) = (∏ τ, (T τ).det) • Pw`. Repeatedly rewrite using `[hq]`. Conclude with `MultilinearMap.map_smul_univ _ _ _`. Establish `hgen : ∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord Dc.y) c p → unitAt 𝔐.ξ p (f l) → (Lat.tens (fun τ => Cusp.detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsGenAt p (∏ τ, (T τ).det ^ (-1 : ℤ))` using `fun p hp hu => tens_isGenAt 𝔐.X Ω 𝔐.ξ _ _ _ p _ fun τ => detLat_isGenAt 𝔐.X Ω 𝔐.ξ 𝔐.Li _ _ (s τ) _ (T τ) p (hsli τ) (hfr τ p (hV p hp hu)).2 (hTs τ)`. Establish `hu₀ : unitAt 𝔐.ξ p₀ (f l)` using `⟨hfl, hreg₀ _, hreg₀ _⟩`.

Establish `ht₀ : (∏ τ, (T τ).det ^ (-1 : ℤ)) ≠ 0` using `(hgen p₀ hp₀ hu₀).1`. Establish `hm₀ : chartMono Dc.y c aMu ≠ 0`. Use `Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ ?_` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.1 hc k' (Finset.mem_univ _)`. Establish `hme : chartMono Dc.y c aMu * e₀ ≠ 0` using `mul_ne_zero hm₀ he₀`.

Establish `hunit : ∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord Dc.y) c p → unitAt 𝔐.ξ p (f l) → unitAt 𝔐.ξ p ((∏ τ, (T τ).det ^ (-1 : ℤ)) / (chartMono Dc.y c aMu * e₀))` using `fun p hp hu => unitAt_div_of_span_eq ht₀ hme ((hgen p hp hu).2.symm.trans (hdeg.2 p trivial c hp))`. Use `⟨(∏ τ, (T τ).det ^ (-1 : ℤ)) / (chartMono Dc.y c aMu * e₀), ⟨div_ne_zero ht₀ hme, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `exists_pow_mul_mem hT hc (hf l) fun p hp hu => (hunit p hp hu).2.1`. Conclude with `exists_pow_mul_mem hT hc (hf l) fun p hp hu => (hunit p hp hu).2.2`. Rewrite using `[htp, smul_smul]`.

Use `congr 1`. Establish `hD : (∏ τ, (T τ).det ^ (-1 : ℤ)) * ∏ τ, (T τ).det = 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun τ _ => ?_` and prove the remaining obligations. Establish `: (T τ).det ≠ 0` using `fun h0 => ht₀ (Finset.prod_eq_zero (Finset.mem_univ τ) (by simp [h0]))`.

Simplify using `[this]`. Generalize the expression as in `(∏ τ, (T τ).det ^ (-1 : ℤ)) = A at hD ⊢`. Generalize the expression as in `(∏ τ, (T τ).det) = B at hD ⊢`. Establish `h1 : A / (chartMono Dc.y c aMu * e₀) * chartMono Dc.y c aMu * B = (A * B) * e₀⁻¹`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[h1, hD, _root_.one_mul]`. Take `⟨f', g', hf', hg', hsum', hP⟩` from `exists_nonzero_cover (chartRing ℤ (segreCoord Dc.y) c).toSubring (fun f₁ => ∃ b : ∀ τ, Fin Dc.N → W τ, (∀ τ, IsAdaptedFrame Dc.y (Dc.W τ) (F τ) hj c f₁ (b τ)) ∧ ∃ u : Ω, IsUnitOn Dc.y c f₁ u ∧ e₀⁻¹ • Pw = (u * chartMono Dc.y c aMu) • PiTensorProduct.tprod Ω fun τ => quotWedge (F …`. Conclude with `⟨k, f', g', hf', hg', hsum', hP⟩`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (S₀ : Finset ℕ) (𝔐 : HodgeCpt Y S₀ Dc.y) (bg sm : CMType H → CMType H ⊕ CMType H) (i : ∀ τ, W τ →ₗ[Ω] 𝔐.Li) (s : CMType H → Fin (Dc.N - Dc.j) → 𝔐.Li) (aMu : K → ℤ) (e₀ : Ω), (∀ τ, Function.Injective (i τ)) → (∀ τ, LinearMap.range (i τ) = 𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)) → (∀ τ, bg τ ≠ sm τ) → (∀ τ, labelRk D (bg τ) = Dc.j) → (∀ τ, labelRk D (sm τ) = Dc.N - Dc.j) → (∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsVB Dc.N ⊤) → (∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsChartOf (segreCoord Dc.y) (Dc.W τ).lat) → (∀ τ, LinearIndependent Ω (s τ)) → (∀ τ, Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) → (Lat.tens (fun τ => Cusp.detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ Dc.y aMu e₀ → ∃ Hd : HodgeData Dc, ∀ τ, Hd.F τ = (𝔐.Vgen (bg τ)).comap (i τ) := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc S₀ 𝔐 bg sm i s aMu e₀ hinj hrange hne hbg hsm hvb hch hsli hsspan hdeg
  classical
  have hT : CoordTie ℤ 𝔐.ξ (segreCoord Dc.y) := 𝔐.tie
  have hVB : ∀ t, (𝔐.V t).IsVB (labelRk D t) (𝔐.Vgen t) := 𝔐.vb
  have hj := Dc.j_le_N
  have hpre : ∀ τ a, ∃ w, i τ w = s τ a := fun τ a => by
    have h : s τ a ∈ LinearMap.range (i τ) := by
      rw [hrange τ]
      exact Submodule.mem_sup_right (hsspan τ ▸ Submodule.subset_span ⟨a, rfl⟩)
    exact h
  choose w hw using hpre
  have he₀ : e₀ ≠ 0 := hdeg.1
  let F : ∀ τ, Submodule Ω (W τ) := fun τ => (𝔐.Vgen (bg τ)).comap (i τ)
  let Pw : PiTensorProduct Ω (fun τ => ⋀[Ω]^(Dc.N - Dc.j) (W τ ⧸ F τ)) :=
    PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω (Dc.N - Dc.j) fun a => (F τ).mkQ (w τ a)
  refine ⟨⟨F, aMu, e₀⁻¹ • Pw, ?_⟩, fun _ => rfl⟩
  intro c hc
  let Q : 𝔐.X.Opens → Prop := fun V => ∃ b : ∀ τ, Fin Dc.N → W τ,
    (∀ τ, Submodule.span Ω (Set.range (b τ)) = ⊤) ∧
    (∀ τ, Submodule.span Ω (Set.range (b τ ∘ headIdx hj)) = F τ) ∧
    (∀ τ a, i τ (b τ (tailIdx hj a)) ∈ 𝔐.Vgen (sm τ)) ∧
    ∀ τ (q : Cpt 𝔐.ξ), q.1 ∈ V →
      (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsFrameAt (b τ) q ∧
      (𝔐.V (sm τ)).IsFrameAt (fun a => i τ (b τ (tailIdx hj a))) q
  have hQ : ∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord Dc.y) c p → ∃ V : 𝔐.X.Opens, p.1 ∈ V ∧ Q V := by
    intro p _
    have hloc := fun τ => exists_block_frame 𝔐.X Ω 𝔐.ξ 𝔐.Li (W τ) (i τ) (𝔐.V (bg τ)) (𝔐.V (sm τ)) (𝔐.Vgen (bg τ)) (𝔐.Vgen (sm τ))
      Dc.N Dc.j hj (hinj τ) (hrange τ) (hbg τ ▸ hVB (bg τ)) (hsm τ ▸ hVB (sm τ)) (hvb τ) p
    choose U hpU b hb1 hb2 hb3 hb4 using hloc
    obtain ⟨V, hpV, hVU⟩ := exists_open_le U hpU
    exact ⟨V, hpV, b, hb1, hb2, hb3, fun τ q hq => hb4 τ q (hVU τ hq)⟩
  obtain ⟨k, f, g, hf, hg, hsum, hl⟩ := exists_cover hT hc Q hQ
  let p₀ : Cpt 𝔐.ξ := ⟨genPt 𝔐.ξ, specializes_rfl⟩
  have hreg₀ : ∀ a : Ω, a ∈ regAt 𝔐.ξ p₀ := TieVB.regAt_genPt hT.gen
  have hp₀ : InChart 𝔐.ξ (segreCoord Dc.y) c p₀ := ⟨hc, fun c' => hreg₀ _⟩
  have key : ∀ l, f l ≠ 0 → ∃ b : ∀ τ, Fin Dc.N → W τ,
      (∀ τ, IsAdaptedFrame Dc.y (Dc.W τ) (F τ) hj c (f l) (b τ)) ∧
      ∃ u : Ω, IsUnitOn Dc.y c (f l) u ∧
        e₀⁻¹ • Pw = (u * chartMono Dc.y c aMu) • PiTensorProduct.tprod Ω fun τ => quotWedge (F τ) hj (b τ) := by
    intro l hfl
    obtain ⟨V, ⟨b, hspan, hhead, hmem, hfr⟩, hV⟩ := hl l
    refine ⟨b, fun τ => ⟨(GlobalTheory.T.segre_chart_bundle 𝔐.X Ω 𝔐.ξ K J Dc.y (W τ) Dc.N (Dc.W τ) _ hT (hvb τ) (hch τ) c (f l) (b τ) hc (hf l) hfl).2
      fun p hp hu => (hfr τ p (hV p hp hu)).1, hspan τ, hhead τ⟩, ?_⟩
    have hex : ∀ τ, ∃ T : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω,
        ∀ a, i τ (b τ (tailIdx hj a)) = ∑ a', T a' a • s τ a' := fun τ => by
      have h : ∀ a, ∃ v : Fin (Dc.N - Dc.j) → Ω, ∑ a', v a' • s τ a' = i τ (b τ (tailIdx hj a)) := fun a =>
        (Submodule.mem_span_range_iff_exists_fun Ω).1 (by rw [hsspan τ]; exact hmem τ a)
      choose v hv using h
      exact ⟨Matrix.of fun a' a => v a a', fun a => (hv a).symm⟩
    choose T hTs using hex
    have hbw : ∀ τ a, b τ (tailIdx hj a) = ∑ a', T τ a' a • w τ a' := fun τ a => hinj τ (by
      rw [hTs, map_sum]
      exact Finset.sum_congr rfl fun a' _ => by rw [map_smul, hw])
    have hq : ∀ τ, quotWedge (F τ) hj (b τ) =
        (T τ).det • exteriorPower.ιMulti Ω (Dc.N - Dc.j) fun a => (F τ).mkQ (w τ a) := fun τ => by
      rw [← iotaMulti_comb]
      unfold quotWedge
      congr 1
      funext a
      rw [hbw, map_sum]
      exact Finset.sum_congr rfl fun a' _ => by rw [map_smul]
    have htp : (PiTensorProduct.tprod Ω fun τ => quotWedge (F τ) hj (b τ)) = (∏ τ, (T τ).det) • Pw := by
      simp_rw [hq]
      exact MultilinearMap.map_smul_univ _ _ _
    have hgen : ∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord Dc.y) c p → unitAt 𝔐.ξ p (f l) →
        (Lat.tens (fun τ => Cusp.detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsGenAt p (∏ τ, (T τ).det ^ (-1 : ℤ)) :=
      fun p hp hu => tens_isGenAt 𝔐.X Ω 𝔐.ξ _ _ _ p _ fun τ => detLat_isGenAt 𝔐.X Ω 𝔐.ξ 𝔐.Li _ _ (s τ) _ (T τ) p (hsli τ)
        (hfr τ p (hV p hp hu)).2 (hTs τ)
    have hu₀ : unitAt 𝔐.ξ p₀ (f l) := ⟨hfl, hreg₀ _, hreg₀ _⟩
    have ht₀ : (∏ τ, (T τ).det ^ (-1 : ℤ)) ≠ 0 := (hgen p₀ hp₀ hu₀).1
    have hm₀ : chartMono Dc.y c aMu ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ ?_
      exact Finset.prod_ne_zero_iff.1 hc k' (Finset.mem_univ _)
    have hme : chartMono Dc.y c aMu * e₀ ≠ 0 := mul_ne_zero hm₀ he₀
    have hunit : ∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord Dc.y) c p → unitAt 𝔐.ξ p (f l) →
        unitAt 𝔐.ξ p ((∏ τ, (T τ).det ^ (-1 : ℤ)) / (chartMono Dc.y c aMu * e₀)) := fun p hp hu =>
      unitAt_div_of_span_eq ht₀ hme ((hgen p hp hu).2.symm.trans (hdeg.2 p trivial c hp))
    refine ⟨(∏ τ, (T τ).det ^ (-1 : ℤ)) / (chartMono Dc.y c aMu * e₀), ⟨div_ne_zero ht₀ hme, ?_, ?_⟩, ?_⟩
    · exact exists_pow_mul_mem hT hc (hf l) fun p hp hu => (hunit p hp hu).2.1
    · exact exists_pow_mul_mem hT hc (hf l) fun p hp hu => (hunit p hp hu).2.2
    · rw [htp, smul_smul]
      congr 1
      have hD : (∏ τ, (T τ).det ^ (-1 : ℤ)) * ∏ τ, (T τ).det = 1 := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun τ _ => ?_
        have : (T τ).det ≠ 0 := fun h0 => ht₀ (Finset.prod_eq_zero (Finset.mem_univ τ) (by simp [h0]))
        simp [this]
      generalize (∏ τ, (T τ).det ^ (-1 : ℤ)) = A at hD ⊢
      generalize (∏ τ, (T τ).det) = B at hD ⊢
      have h1 : A / (chartMono Dc.y c aMu * e₀) * chartMono Dc.y c aMu * B = (A * B) * e₀⁻¹ := by
        field_simp
      rw [h1, hD, _root_.one_mul]
  obtain ⟨f', g', hf', hg', hsum', hP⟩ := exists_nonzero_cover (chartRing ℤ (segreCoord Dc.y) c).toSubring
    (fun f₁ => ∃ b : ∀ τ, Fin Dc.N → W τ,
      (∀ τ, IsAdaptedFrame Dc.y (Dc.W τ) (F τ) hj c f₁ (b τ)) ∧
      ∃ u : Ω, IsUnitOn Dc.y c f₁ u ∧
        e₀⁻¹ • Pw = (u * chartMono Dc.y c aMu) • PiTensorProduct.tprod Ω fun τ => quotWedge (F τ) hj (b τ))
    f g hf hg hsum key
  exact ⟨k, f', g', hf', hg', hsum', hP⟩

end GlobalTheory.CompanionTheory.Ar.BigBlock
