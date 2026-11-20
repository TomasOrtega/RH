import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsChartBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

namespace ChartFrame

/- English proof (translation)
Establish `hb0 : b ≠ 0` using `right_ne_zero_of_mul h0`. Unfold `GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.locSub`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `y (hy | hy)`. Conclude with `Subring.subset_closure (Set.mem_union_left _ hy)`.

Rewrite `hy` using `[Set.mem_singleton_iff]`. Rewrite using `[hy, show a⁻¹ = b * (a * b)⁻¹ by rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hb0, mul_one]]`. Conclude with `mul_mem (Subring.subset_closure (Set.mem_union_left _ hb)) (Subring.subset_closure (Set.mem_union_right _ (Set.mem_singleton _)))`.
-/
theorem locSub_le_of_mul {F : Type} [Field F] {R : Subring F} {a b : F} (ha : a ∈ R) (hb : b ∈ R)
    (h0 : a * b ≠ 0) : locSub R a ≤ locSub R (a * b) := by
  have hb0 : b ≠ 0 := right_ne_zero_of_mul h0
  unfold GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.locSub
  rw [Subring.closure_le]
  rintro y (hy | hy)
  · exact Subring.subset_closure (Set.mem_union_left _ hy)
  · rw [Set.mem_singleton_iff] at hy
    rw [hy, show a⁻¹ = b * (a * b)⁻¹ by rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hb0, mul_one]]
    exact mul_mem (Subring.subset_closure (Set.mem_union_left _ hb))
      (Subring.subset_closure (Set.mem_union_right _ (Set.mem_singleton _)))

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.Ar.unitAt at hf hg ⊢`. Take `⟨hf0, hf1, hf2⟩` from `hf`. Take `⟨hg0, hg1, hg2⟩` from `hg`. Use `⟨mul_ne_zero hf0 hg0, mul_mem hf1 hg1, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv]`.

Conclude with `mul_mem hf2 hg2`.
-/
theorem unitAt_mul' {p : Cpt ξ} {f g : Ω} (hf : unitAt ξ p f) (hg : unitAt ξ p g) :
    unitAt ξ p (f * g) := by
  unfold GlobalTheory.CompanionTheory.Ar.unitAt at hf hg ⊢
  obtain ⟨hf0, hf1, hf2⟩ := hf
  obtain ⟨hg0, hg1, hg2⟩ := hg
  refine ⟨mul_ne_zero hf0 hg0, mul_mem hf1 hg1, ?_⟩
  rw [mul_inv]
  exact mul_mem hf2 hg2

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.prod_empty]`. Unfold `GlobalTheory.CompanionTheory.Ar.unitAt`. Use `⟨one_ne_zero, one_mem _, ?_⟩` and prove the remaining obligations.

Rewrite using `[inv_one]`. Conclude with `one_mem _`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`. Conclude with `unitAt_mul' (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem unitAt_prod' {p : Cpt ξ} {ι : Type} (s : Finset ι) (f : ι → Ω) (h : ∀ i ∈ s, unitAt ξ p (f i)) :
    unitAt ξ p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    unfold GlobalTheory.CompanionTheory.Ar.unitAt
    refine ⟨one_ne_zero, one_mem _, ?_⟩
    rw [inv_one]
    exact one_mem _
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitAt_mul' (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Establish `hext : ∀ l : Fin r, ∃ g : Module.Dual Ω E, g.comp (Submodule.span Ω (Set.range β)).subtype = (Module.Basis.span hβ).coord l` using `fun l => LinearMap.exists_extend ((Module.Basis.span hβ).coord l)`. Use `choose w hw using hext`. Use `⟨w, fun l l' => ?_⟩` and prove the remaining obligations. Establish `h1 : w l (β l') = (Module.Basis.span hβ).coord l (Module.Basis.span hβ l')`. Rewrite using `[← hw l, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]`.

Rewrite using `[h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]`. Break down `eq_or_ne l l' with rfl | hne` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[hne, hne.symm]`.
-/
theorem exists_dual_family {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} {β : Fin r → E}
    (hβ : LinearIndependent Ω β) :
    ∃ w : Fin r → Module.Dual Ω E, ∀ l l', w l (β l') = (1 : Matrix (Fin r) (Fin r) Ω) l l' := by
  classical
  have hext : ∀ l : Fin r, ∃ g : Module.Dual Ω E,
      g.comp (Submodule.span Ω (Set.range β)).subtype = (Module.Basis.span hβ).coord l :=
    fun l => LinearMap.exists_extend ((Module.Basis.span hβ).coord l)
  choose w hw using hext
  refine ⟨w, fun l l' => ?_⟩
  have h1 : w l (β l') = (Module.Basis.span hβ).coord l (Module.Basis.span hβ l') := by
    rw [← hw l, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]
  rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
  rcases eq_or_ne l l' with rfl | hne
  · simp
  · simp [hne, hne.symm]

end ChartFrame

open ChartFrame ChartTie in

/- English proof (translation)
Introduce `X Ω _ ξ E _ _ κ x r V L m n φ b c p hCT _hgen hVB hTw hb hIn`. Take `⟨hbli, hbV⟩` from `hb`. Establish `hx0 : x c ≠ 0`. Unfold `GlobalTheory.CompanionTheory.Ar.InChart at hIn`. Conclude with `hIn.1`.

Establish `hxm : x c ^ m ≠ 0` using `pow_ne_zero m hx0`. Unfold `GlobalTheory.CompanionTheory.Ar.FlagBun.IsTwistGen at hTw`. Take `⟨hTw1, hTw2⟩` from `hTw`. Unfold `GlobalTheory.CompanionTheory.Ar.Lat.IsVB GlobalTheory.CompanionTheory.Ar.Lat.IsVBOn at hVB`. Take `⟨U, hpU, b', hb'V, hfr⟩` from `hVB p (Set.mem_univ p)`.

Establish `hF` using `hfr p (Set.mem_univ p) hpU`. Unfold `GlobalTheory.CompanionTheory.Ar.Lat.IsFrameAt at hF`. Take `⟨hb'li, hLp⟩` from `hF`. Take `⟨w, hw⟩` from `exists_dual_family hb'li`. Establish `hcoord : ∀ e ∈ Submodule.span Ω (Set.range b'), e = ∑ k, w k e • b' k`.

Introduce `e he`. Take `⟨cf, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun Ω).1 he`. Establish `hwc : ∀ k, w k (∑ i, cf i • b' i) = cf k`. Introduce `k`. Simplify using `[hw, Matrix.one_apply]`.

Conclude with `(Finset.sum_congr rfl fun k _ => by rw [hwc k]).symm`. Establish `hbexp : ∀ l, b l = ∑ k, w k (b l) • b' k` using `fun l => hcoord _ (by rw [hb'V, ← hbV]; exact Submodule.subset_span ⟨l, rfl⟩)`. Establish `hdet : (Matrix.of fun k l => w k (b l)).det ≠ 0`. Introduce `hdet0`. Take `⟨v, hv0, hTv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet0`.

Apply `hv0` to reduce the goal to its premises. Establish `hsum : ∑ l, v l • b l = 0`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`.

Use `congr 1`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply]`. Conclude with `Finset.sum_congr rfl fun l _ => mul_comm _ _`. Use `_ = 0 := by simp [hTv]`. Conclude with `funext (Fintype.linearIndependent_iff.1 hbli v hsum)`.

Establish `hb'Lp : ∀ k, b' k ∈ L p` using `fun k => by`. Rewrite using `[hLp]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Establish `hMreg : ∀ j k, φ j (b' k) / x c ^ m ∈ regAt ξ p` using `fun j k => hTw1 j p c hIn (b' k) (hb'Lp k)`. Establish `hwreg : ∀ l, ∀ e ∈ L p, w l e ∈ regAt ξ p`.

Introduce `l e he`. Rewrite `he` using `[hLp]`. Take `⟨cf, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 he`. Rewrite using `[map_sum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Subring.smul_def, map_smul, hw, smul_eq_mul]`. Use `mul_mem (cf i).2 ?_` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Establish `hN : ∀ l, ∃ gv : Fin n → Ω, (∀ j, gv j ∈ regAt ξ p) ∧ ∀ e ∈ L p, w l e = ∑ j, gv j * (φ j e / x c ^ m)` using `fun l => hTw2 p c hIn (w l) (hwreg l)`. Use `choose gv hgvreg hgv using hN`. Establish `hNM : (Matrix.of fun l j => gv l j) * (Matrix.of fun j k => φ j (b' k) / x c ^ m) = 1`. Use extensionality with `l l'`.

Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[← hgv l (b' l') (hb'Lp l'), hw]`. Establish `hreg : ∀ a ∈ regAt ξ p, ∃ s ∈ chartSub x c, unitAt ξ p s ∧ a ∈ locSub (chartSub x c) s`. Introduce `a ha`.

Take `⟨s, hs, hsu, hsa⟩` from `(GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x hCT c p hIn a).1 ha`. Establish `hs0 : s ≠ 0`. Unfold `GlobalTheory.CompanionTheory.Ar.unitAt at hsu`. Conclude with `hsu.1`. Use `⟨s, by unfold GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartSub; exact hs, hsu, ?_⟩` and prove the remaining obligations.

Unfold `GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.locSub`. Rewrite using `[show a = s * a * s⁻¹ by rw [mul_comm s a, mul_assoc, mul_inv_cancel₀ hs0, mul_one]]`. Conclude with `mul_mem (Subring.subset_closure (Set.mem_union_left _ (by unfold GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartSub; exact hsa))) (Subring.subset_closure (Set.mem_union_right _ (Set.mem_singleton _)))`. Establish `hent : ∀ i : (Fin n × Fin r) ⊕ (Fin r × Fin n), Sum.elim (fun jk => φ jk.1 (b' jk.2) / x c ^ m) (fun lj => gv lj.1 lj.2) i ∈ regAt ξ p`. Introduce and unpack `(⟨j, k⟩ | ⟨l, j⟩)`.

Conclude with `hMreg j k`. Conclude with `hgvreg l j`. Use `choose s hsR hsU hsloc using fun i => hreg _ (hent i)`. Establish `hgU : unitAt ξ p (∏ i, s i)` using `unitAt_prod' _ _ fun i _ => hsU i`. Establish `hgR : (∏ i, s i) ∈ chartSub x c` using `prod_mem fun i _ => hsR i`.

Establish `hg0 : (∏ i, s i) ≠ 0`. Establish `h` using `hgU`. Unfold `GlobalTheory.CompanionTheory.Ar.unitAt at h`. Conclude with `h.1`. Establish `hmono : ∀ i, locSub (chartSub x c) (s i) ≤ locSub (chartSub x c) (∏ i, s i)`.

Introduce `i`. Establish `hsplit` using `Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i)`. Rewrite using `[← hsplit]`. Conclude with `locSub_le_of_mul (hsR i) (prod_mem fun j _ => hsR j) (by rw [hsplit]; exact hg0)`. Use `⟨∏ i, s i, hgR, hgU, Matrix.of fun k l => w k (b l), Matrix.of fun j k => φ j (b' k) / x c ^ m, Matrix.of fun l j => gv l j, hdet, ?_, ?_, hNM, ?_⟩` and prove the remaining obligations.

Introduce `j k`. Simplify using `only [Matrix.of_apply]`. Conclude with `hmono _ (hsloc (Sum.inl (j, k)))`. Introduce `l j`. Simplify using `only [Matrix.of_apply]`.

Conclude with `hmono _ (hsloc (Sum.inr (l, j)))`. Introduce `j l`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply]`. Use `conv_lhs => rw [hbexp l]`.

Rewrite using `[map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul]`. Use `first`. Consider the case `(rw [div_mul_eq_mul_div, mul_div_assoc', mul_comm (x c ^ m), mul_div_assoc, div_self hxm, mul_one, mul_comm])`.

Consider the case `(field_simp; ring)`. Consider the case `field_simp`.
-/
theorem exists_chart_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (r : ℕ) (V : Submodule Ω E) (L : Lat ξ E) (m n : ℕ) (φ : Fin n → Module.Dual Ω E) (b : Fin r → E) (c : κ) (p : Cpt ξ), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → L.IsVB r V → IsTwistGen ξ x L m φ → (LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = V) → InChart ξ x c p → ∃ g ∈ chartSub x c, unitAt ξ p g ∧ ∃ (T : Matrix (Fin r) (Fin r) Ω) (M : Matrix (Fin n) (Fin r) Ω) (N : Matrix (Fin r) (Fin n) Ω), T.det ≠ 0 ∧ (∀ j l, M j l ∈ locSub (chartSub x c) g) ∧ (∀ l j, N l j ∈ locSub (chartSub x c) g) ∧ N * M = 1 ∧ ∀ j l, φ j (b l) = x c ^ m * (M * T) j l := by
  intro X Ω _ ξ E _ _ κ x r V L m n φ b c p hCT _hgen hVB hTw hb hIn
  classical
  obtain ⟨hbli, hbV⟩ := hb
  have hx0 : x c ≠ 0 := by
    unfold GlobalTheory.CompanionTheory.Ar.InChart at hIn
    exact hIn.1
  have hxm : x c ^ m ≠ 0 := pow_ne_zero m hx0
  unfold GlobalTheory.CompanionTheory.Ar.FlagBun.IsTwistGen at hTw
  obtain ⟨hTw1, hTw2⟩ := hTw
  unfold GlobalTheory.CompanionTheory.Ar.Lat.IsVB GlobalTheory.CompanionTheory.Ar.Lat.IsVBOn at hVB
  obtain ⟨U, hpU, b', hb'V, hfr⟩ := hVB p (Set.mem_univ p)
  have hF := hfr p (Set.mem_univ p) hpU
  unfold GlobalTheory.CompanionTheory.Ar.Lat.IsFrameAt at hF
  obtain ⟨hb'li, hLp⟩ := hF
  obtain ⟨w, hw⟩ := exists_dual_family hb'li
  have hcoord : ∀ e ∈ Submodule.span Ω (Set.range b'), e = ∑ k, w k e • b' k := by
    intro e he
    obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 he
    have hwc : ∀ k, w k (∑ i, cf i • b' i) = cf k := by
      intro k
      simp [hw, Matrix.one_apply]
    exact (Finset.sum_congr rfl fun k _ => by rw [hwc k]).symm
  have hbexp : ∀ l, b l = ∑ k, w k (b l) • b' k := fun l =>
    hcoord _ (by rw [hb'V, ← hbV]; exact Submodule.subset_span ⟨l, rfl⟩)
  have hdet : (Matrix.of fun k l => w k (b l)).det ≠ 0 := by
    intro hdet0
    obtain ⟨v, hv0, hTv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
    apply hv0
    have hsum : ∑ l, v l • b l = 0 := by
      calc ∑ l, v l • b l = ∑ l, v l • ∑ k, w k (b l) • b' k :=
            Finset.sum_congr rfl fun l _ => by rw [← hbexp l]
        _ = ∑ l, ∑ k, (v l * w k (b l)) • b' k := by simp only [Finset.smul_sum, smul_smul]
        _ = ∑ k, ∑ l, (v l * w k (b l)) • b' k := Finset.sum_comm
        _ = ∑ k, (Matrix.mulVec (Matrix.of fun k l => w k (b l)) v) k • b' k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← Finset.sum_smul]
            congr 1
            simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
            exact Finset.sum_congr rfl fun l _ => mul_comm _ _
        _ = 0 := by simp [hTv]
    exact funext (Fintype.linearIndependent_iff.1 hbli v hsum)
  have hb'Lp : ∀ k, b' k ∈ L p := fun k => by
    rw [hLp]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hMreg : ∀ j k, φ j (b' k) / x c ^ m ∈ regAt ξ p := fun j k =>
    hTw1 j p c hIn (b' k) (hb'Lp k)
  have hwreg : ∀ l, ∀ e ∈ L p, w l e ∈ regAt ξ p := by
    intro l e he
    rw [hLp] at he
    obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
    rw [map_sum]
    refine sum_mem fun i _ => ?_
    rw [Subring.smul_def, map_smul, hw, smul_eq_mul]
    refine mul_mem (cf i).2 ?_
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hN : ∀ l, ∃ gv : Fin n → Ω, (∀ j, gv j ∈ regAt ξ p) ∧
      ∀ e ∈ L p, w l e = ∑ j, gv j * (φ j e / x c ^ m) := fun l =>
    hTw2 p c hIn (w l) (hwreg l)
  choose gv hgvreg hgv using hN
  have hNM : (Matrix.of fun l j => gv l j) * (Matrix.of fun j k => φ j (b' k) / x c ^ m) = 1 := by
    ext l l'
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [← hgv l (b' l') (hb'Lp l'), hw]
  have hreg : ∀ a ∈ regAt ξ p, ∃ s ∈ chartSub x c, unitAt ξ p s ∧ a ∈ locSub (chartSub x c) s := by
    intro a ha
    obtain ⟨s, hs, hsu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x hCT c p hIn a).1 ha
    have hs0 : s ≠ 0 := by
      unfold GlobalTheory.CompanionTheory.Ar.unitAt at hsu
      exact hsu.1
    refine ⟨s, by unfold GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartSub; exact hs, hsu, ?_⟩
    unfold GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.locSub
    rw [show a = s * a * s⁻¹ by rw [mul_comm s a, mul_assoc, mul_inv_cancel₀ hs0, mul_one]]
    exact mul_mem
      (Subring.subset_closure (Set.mem_union_left _ (by unfold GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartSub; exact hsa)))
      (Subring.subset_closure (Set.mem_union_right _ (Set.mem_singleton _)))
  have hent : ∀ i : (Fin n × Fin r) ⊕ (Fin r × Fin n),
      Sum.elim (fun jk => φ jk.1 (b' jk.2) / x c ^ m) (fun lj => gv lj.1 lj.2) i ∈ regAt ξ p := by
    rintro (⟨j, k⟩ | ⟨l, j⟩)
    · exact hMreg j k
    · exact hgvreg l j
  choose s hsR hsU hsloc using fun i => hreg _ (hent i)
  have hgU : unitAt ξ p (∏ i, s i) := unitAt_prod' _ _ fun i _ => hsU i
  have hgR : (∏ i, s i) ∈ chartSub x c := prod_mem fun i _ => hsR i
  have hg0 : (∏ i, s i) ≠ 0 := by
    have h := hgU
    unfold GlobalTheory.CompanionTheory.Ar.unitAt at h
    exact h.1
  have hmono : ∀ i, locSub (chartSub x c) (s i) ≤ locSub (chartSub x c) (∏ i, s i) := by
    intro i
    have hsplit := Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i)
    rw [← hsplit]
    exact locSub_le_of_mul (hsR i) (prod_mem fun j _ => hsR j) (by rw [hsplit]; exact hg0)
  refine ⟨∏ i, s i, hgR, hgU, Matrix.of fun k l => w k (b l),
    Matrix.of fun j k => φ j (b' k) / x c ^ m, Matrix.of fun l j => gv l j, hdet, ?_, ?_, hNM, ?_⟩
  · intro j k
    simp only [Matrix.of_apply]
    exact hmono _ (hsloc (Sum.inl (j, k)))
  · intro l j
    simp only [Matrix.of_apply]
    exact hmono _ (hsloc (Sum.inr (l, j)))
  · intro j l
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    conv_lhs => rw [hbexp l]
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul]
    first
      | (rw [div_mul_eq_mul_div, mul_div_assoc', mul_comm (x c ^ m), mul_div_assoc, div_self hxm,
          mul_one, mul_comm])
      | (field_simp; ring)
      | field_simp

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
