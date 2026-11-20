import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LatticeSpanMembership
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.UWLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Establish `hloc` using `fun τ : X.Ψ => FramePeriod.exists_loc τ.1 X.Gm X.Gm_herm X.p0 (mat x τ) (hx τ).1 (hx τ).2`. Establish `hpos` using `im_neg_half_pos X`. Use `set ξ : E := -(X.κ0 / 2) with hξd`. Establish `hξ : cc ξ = -ξ`. Establish `h` using `X.ξ0_im`.

Unfold `cc at h ⊢`. Apply the tactic sequence `rcases X.κ0_xi with h' | h' <;> rw [hξd, h'] <;>`. Apply the tactic sequence `simp only [map_neg, map_div₀, map_mul, map_ofNat, h] <;> ring`. Use `choose Hl hH hp hI using fun τ => (hloc τ).2`. Use `⟨Matrix.of fun k l => if (idx k).1 = (idx l).1 then ((2 * ((idx k).1.1 ξ).im : ℝ) : ℂ) * Hl (idx k).1 (idx k).2 (idx l).2 else 0, ?_, ?_⟩` and prove the remaining obligations.

Introduce `z hz`. Rewrite using `[FramePeriod.hermForm_block idx (fun τ : X.Ψ => 2 * (τ.1 ξ).im) Hl, Complex.re_sum]`. Simplify using `only [Complex.re_ofReal_mul]`. Take `⟨k, hk⟩` from `Function.ne_iff.1 hz`. Use `Finset.sum_pos' (fun τ _ => mul_nonneg (by linarith [hpos τ]) ?_) ⟨(idx k).1, Finset.mem_univ _, mul_pos (by linarith [hpos (idx k).1]) (hp _ _ ?_)⟩` and prove the remaining obligations.

Distinguish the cases in `h : (fun a => z (idx.symm (τ, a))) = 0`. Rewrite using `[h]`. Simplify using `[hermForm]`. Conclude with `(hp _ _ h).le`. Introduce `h`.

Apply `hk` to reduce the goal to its premises. Simplify using `using congrFun h (idx k).2`. Introduce `v w`. Rewrite using `[FramePeriod.hermForm_block idx (fun τ : X.Ψ => 2 * (τ.1 ξ).im) Hl, Complex.im_sum, EF_def, FramePeriod.trace_re X.Ψ X.cmType]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Establish `hs : ∀ u, (fun a => pv X idx x u (idx.symm (τ, a))) = FramePeriod.locPer τ.1 X.Gm X.p0 (mat x τ) (Data.emb τ.1 u)`. Introduce `u`. Use function extensionality and compare the values at `a`. Simplify using `only [pv, Function.comp, Equiv.apply_symm_apply]`. Both sides reduce to the same expression.

Rewrite using `[hs, hs, Complex.im_ofReal_mul, hI, map_mul, ← hermC_emb]`. Establish `h2 : (τ.1 ξ).re = 0`. Establish `h3` using `congrArg Complex.re (emb_cc τ.1 ξ)`. Rewrite `h3` using `[hξ, map_neg, Complex.neg_re, Complex.conj_re]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[Complex.mul_re, h2]`. Express the relevant statement in the definitionally equal form `_ * -(hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 w)).im = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_pos_form (X : Data E r) {g : ℕ} (idx : Fin g ≃ X.Ψ × Fin r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      ∀ u v, (hermForm Hm (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ) := by
  have hloc := fun τ : X.Ψ => FramePeriod.exists_loc τ.1 X.Gm X.Gm_herm X.p0 (mat x τ) (hx τ).1 (hx τ).2
  have hpos := im_neg_half_pos X
  set ξ : E := -(X.κ0 / 2) with hξd
  have hξ : cc ξ = -ξ := by
    have h := X.ξ0_im
    unfold cc at h ⊢
    rcases X.κ0_xi with h' | h' <;> rw [hξd, h'] <;>
      simp only [map_neg, map_div₀, map_mul, map_ofNat, h] <;> ring
  choose Hl hH hp hI using fun τ => (hloc τ).2
  refine ⟨Matrix.of fun k l => if (idx k).1 = (idx l).1 then
    ((2 * ((idx k).1.1 ξ).im : ℝ) : ℂ) * Hl (idx k).1 (idx k).2 (idx l).2 else 0, ?_, ?_⟩
  · intro z hz
    rw [FramePeriod.hermForm_block idx (fun τ : X.Ψ => 2 * (τ.1 ξ).im) Hl, Complex.re_sum]
    simp only [Complex.re_ofReal_mul]
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hz
    refine Finset.sum_pos' (fun τ _ => mul_nonneg (by linarith [hpos τ]) ?_)
      ⟨(idx k).1, Finset.mem_univ _, mul_pos (by linarith [hpos (idx k).1]) (hp _ _ ?_)⟩
    · by_cases h : (fun a => z (idx.symm (τ, a))) = 0
      · rw [h]; simp [hermForm]
      · exact (hp _ _ h).le
    · intro h
      apply hk
      simpa using congrFun h (idx k).2
  · intro v w
    rw [FramePeriod.hermForm_block idx (fun τ : X.Ψ => 2 * (τ.1 ξ).im) Hl, Complex.im_sum, EF_def,
      FramePeriod.trace_re X.Ψ X.cmType]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hs : ∀ u, (fun a => pv X idx x u (idx.symm (τ, a))) =
        FramePeriod.locPer τ.1 X.Gm X.p0 (mat x τ) (Data.emb τ.1 u) := by
      intro u
      funext a
      simp only [pv, Function.comp, Equiv.apply_symm_apply]
      rfl
    rw [hs, hs, Complex.im_ofReal_mul, hI, map_mul, ← hermC_emb]
    have h2 : (τ.1 ξ).re = 0 := by
      have h3 := congrArg Complex.re (emb_cc τ.1 ξ)
      rw [hξ, map_neg, Complex.neg_re, Complex.conj_re] at h3
      linarith
    rw [Complex.mul_re, h2]
    change _ * -(hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 w)).im = _
    ring

/- English proof (translation)
Establish `hadd : ∀ z w, hermForm (A + B) z w = hermForm A z w + hermForm B z w`. Introduce `z w`. Simplify using `[hermForm, add_mulVec]`. Establish `h1 : ∀ z, z ∈ Submodule.span ℝ (Set.range P) → ∀ w, w ∈ Submodule.span ℝ (Set.range P) → (hermForm (A + B) z w).im = 0`. Generalize the expression as in `hC : A + B = C at hadd`.

Introduce `z hz w hw`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨a, rfl⟩` from `hz`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem w hw`. Take `⟨b, rfl⟩` from `hw`. Rewrite using `[hadd, Complex.add_im, h]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => simp [hermForm]`.

Consider the case `add v w _ _ hv hw`. Simplify using `only [hermForm, star_add, mulVec_add, dotProduct_add, Complex.add_im] at hv hw ⊢`. Rewrite using `[hv, hw, add_zero]`. Consider the case `smul t w _ hw`. Simplify using `only [hermForm, star_smul, mulVec_smul, dotProduct_smul, Complex.smul_im] at hw ⊢`.

Rewrite using `[hw, smul_zero]`. Consider the case `zero => simp [hermForm]`. Consider the case `add u v _ _ hu hv`. Simplify using `only [hermForm, add_dotProduct, Complex.add_im] at hu hv ⊢`. Rewrite using `[hu, hv, add_zero]`.

Consider the case `smul t v _ hv`. Simplify using `only [hermForm, smul_dotProduct, Complex.smul_im] at hv ⊢`. Rewrite using `[hv, smul_zero]`. Establish `hz : (fun _ => 1 : Fin g → ℂ) ≠ 0` using `fun h0 => by`. Simplify using `using congrFun h0 (Classical.arbitrary _)`.

Establish `h2` using `h1 (I • (fun _ => 1 : Fin g → ℂ)) (hP ▸ Submodule.mem_top) (fun _ => 1) (hP ▸ Submodule.mem_top)`. Establish `h3 : hermForm (A + B) (I • (fun _ => 1 : Fin g → ℂ)) (fun _ => 1) = I * hermForm (A + B) (fun _ => 1) (fun _ => 1)`. Simplify using `only [hermForm, smul_dotProduct, smul_eq_mul]`. Rewrite `h2` using `[h3, hadd]`. Use `hA _ hz` as an intermediate fact.

Use `hB _ hz` as an intermediate fact. Simplify using `at h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_opposite {g : ℕ} [Nonempty (Fin g)] {J : Type} (P : J → Fin g → ℂ)
    (hP : Submodule.span ℝ (Set.range P) = ⊤) (A B : Matrix (Fin g) (Fin g) ℂ)
    (hA : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm A z z).re)
    (hB : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm B z z).re)
    (h : ∀ a b, (hermForm A (P a) (P b)).im = -(hermForm B (P a) (P b)).im) : False := by
  have hadd : ∀ z w, hermForm (A + B) z w = hermForm A z w + hermForm B z w := by
    intro z w; simp [hermForm, add_mulVec]
  have h1 : ∀ z, z ∈ Submodule.span ℝ (Set.range P) → ∀ w, w ∈ Submodule.span ℝ (Set.range P) →
      (hermForm (A + B) z w).im = 0 := by
    generalize hC : A + B = C at hadd
    intro z hz w hw
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨b, rfl⟩ := hw
        rw [hadd, Complex.add_im, h]; ring
      | zero => simp [hermForm]
      | add v w _ _ hv hw =>
        simp only [hermForm, star_add, mulVec_add, dotProduct_add, Complex.add_im] at hv hw ⊢
        rw [hv, hw, add_zero]
      | smul t w _ hw =>
        simp only [hermForm, star_smul, mulVec_smul, dotProduct_smul, Complex.smul_im] at hw ⊢
        rw [hw, smul_zero]
    | zero => simp [hermForm]
    | add u v _ _ hu hv =>
      simp only [hermForm, add_dotProduct, Complex.add_im] at hu hv ⊢
      rw [hu, hv, add_zero]
    | smul t v _ hv =>
      simp only [hermForm, smul_dotProduct, Complex.smul_im] at hv ⊢
      rw [hv, smul_zero]
  have hz : (fun _ => 1 : Fin g → ℂ) ≠ 0 := fun h0 => by
    simpa using congrFun h0 (Classical.arbitrary _)
  have h2 := h1 (I • (fun _ => 1 : Fin g → ℂ)) (hP ▸ Submodule.mem_top) (fun _ => 1) (hP ▸ Submodule.mem_top)
  have h3 : hermForm (A + B) (I • (fun _ => 1 : Fin g → ℂ)) (fun _ => 1) = I * hermForm (A + B) (fun _ => 1) (fun _ => 1) := by
    simp only [hermForm, smul_dotProduct, smul_eq_mul]
  rw [h3, hadd] at h2
  have := hA _ hz
  have := hB _ hz
  simp at h2
  linarith

/- English proof (translation)
Simplify using `only [EF_def, ← map_sub]`. Use `congr 1`. Simplify using `only [herm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]`.
-/
theorem EF_sub_left (X : Data E r) (u v w : Fin r → E) : EF X (u - v) w = EF X u w - EF X v w := by
  simp only [EF_def, ← map_sub]
  congr 1
  simp only [herm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

/- English proof (translation)
Simplify using `only [EF_def, ← map_add]`. Use `congr 1`. Simplify using `only [herm, cc, Pi.add_apply, map_add, Finset.sum_add_distrib, mul_add]`.
-/
theorem EF_add_right (X : Data E r) (u v w : Fin r → E) : EF X u (v + w) = EF X u v + EF X u w := by
  simp only [EF_def, ← map_add]
  congr 1
  simp only [herm, cc, Pi.add_apply, map_add, Finset.sum_add_distrib, mul_add]

/- English proof (translation)
Simplify using `only [EF_def]`. Rewrite using `[← smul_eq_mul (N : ℚ), ← map_smul]`. Use `congr 1`. Simplify using `only [herm, Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_natCast, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem EF_nat_left (X : Data E r) (N : ℕ) (u w : Fin r → E) : EF X ((N : E) • u) w = N * EF X u w := by
  simp only [EF_def]
  rw [← smul_eq_mul (N : ℚ), ← map_smul]
  congr 1
  simp only [herm, Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_natCast, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Use `⟨X.Λ_fg, fun x => ⟨fun hx y hy => ?_, fun hx => ?_⟩⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `(hf x).1 hx`. Take `⟨b, rfl⟩` from `(hf y).1 hy`. Conclude with `⟨_, (hE a b).symm⟩`. Use `choose k hk using fun b => hx (f b) ((hf _).2 ⟨b, rfl⟩)`.

Set `φ : D.La →+ ℤ` to `AddMonoidHom.mk' k fun b b' => by`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Rewrite using `[Int.cast_add, ← hk, ← hk, ← hk, map_add, EF_add_right]`. Take `⟨a, ha⟩` from `D.unimod.2 φ.toIntLinearMap`. Establish `h0 : ∀ b, EF X (x - f a) (f b) = 0` using `fun b => by`.

Rewrite using `[EF_sub_left, ← hE, ha, hk]`. Conclude with `sub_self _`. Take `⟨N, hN, hm⟩` from `LatticeSpanMembership.exists_nat_smul_mem (X := X) (x - f a)`. Take `⟨a', ha'⟩` from `(hf _).1 hm`. Establish `h1 : a' = 0`.

Apply `D.unimod.1` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use extensionality with `b`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Rewrite using `[hE, ha', EF_nat_left, h0]`.

Simplify using the standard rewrite rules. Rewrite `ha'` using `[h1, map_zero, eq_comm, smul_eq_zero]`. Establish `h2` using `ha'.resolve_left (by exact_mod_cast hN.ne')`. Conclude with `(hf _).2 ⟨a, (sub_eq_zero.1 h2).symm⟩`.
-/
theorem selfD_of_unimod {H : Host E} (X : Data E r) (D : Datum H) (f : D.La →ₗ[𝓞 E] (Fin r → E))
    (hf : ∀ v, v ∈ X.Λ ↔ ∃ a, f a = v) (hE : ∀ a b, ((D.EF a b : ℤ) : ℚ) = EF X (f a) (f b)) :
    SelfD X X.Λ := by
  refine ⟨X.Λ_fg, fun x => ⟨fun hx y hy => ?_, fun hx => ?_⟩⟩
  · obtain ⟨a, rfl⟩ := (hf x).1 hx
    obtain ⟨b, rfl⟩ := (hf y).1 hy
    exact ⟨_, (hE a b).symm⟩
  · choose k hk using fun b => hx (f b) ((hf _).2 ⟨b, rfl⟩)
    let φ : D.La →+ ℤ := AddMonoidHom.mk' k fun b b' => by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_add, ← hk, ← hk, ← hk, map_add, EF_add_right]
    obtain ⟨a, ha⟩ := D.unimod.2 φ.toIntLinearMap
    have h0 : ∀ b, EF X (x - f a) (f b) = 0 := fun b => by
      rw [EF_sub_left, ← hE, ha, hk]
      exact sub_self _
    obtain ⟨N, hN, hm⟩ := LatticeSpanMembership.exists_nat_smul_mem (X := X) (x - f a)
    obtain ⟨a', ha'⟩ := (hf _).1 hm
    have h1 : a' = 0 := by
      apply D.unimod.1
      rw [map_zero]
      ext b
      apply Int.cast_injective (α := ℚ)
      rw [hE, ha', EF_nat_left, h0]
      simp
    rw [h1, map_zero, eq_comm, smul_eq_zero] at ha'
    have h2 := ha'.resolve_left (by exact_mod_cast hN.ne')
    exact (hf _).2 ⟨a, (sub_eq_zero.1 h2).symm⟩

/- English proof (translation)
Apply `D.unimod.1` to reduce the goal to its premises. Use extensionality with `y`. Use `congrArg (fun v => D.EF v y) h` as an intermediate fact. Simplify using `only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at this`. Conclude with `mul_left_cancel₀ (by exact_mod_cast hn) this`.
-/
theorem nsmul_cancel {H : Host E} (D : Datum H) {n : ℕ} (hn : n ≠ 0) {a b : D.La} (h : n • a = n • b) : a = b := by
  apply D.unimod.1
  ext y
  have := congrArg (fun v => D.EF v y) h
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at this
  exact mul_left_cancel₀ (by exact_mod_cast hn) this

/- English proof (translation)
Take `⟨m, hm⟩ : l.M ∣ l.M'` from `Nat.dvd_lcm_left _ _`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Establish `h3` using `l.three_le`. Conclude with `Nat.lcm_ne_zero (by omega) l.A_pos.ne' (hm.trans (mul_zero _))`.

Use `⟨fun a => (hf _).2 ⟨_, rfl⟩, fun a _ ⟨u, hu, hau⟩ => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨b, rfl⟩` from `(hf u).1 hu`. Establish `h1 : t a = l.M • b` using `hinj (by rw [map_nsmul]; exact hau)`. Take `⟨b', hb'⟩` from `(ht (m • a)).1 ⟨b, by rw [map_nsmul, h1, hm, mul_comm, mul_smul]⟩`. Conclude with `⟨b', nsmul_cancel Dw hm0 (by rw [hb', hm, mul_comm, mul_smul])⟩`.

Use `Submodule.smul_induction_on hv (fun s hs' w hw => ?_) ?_` and prove the remaining obligations. Take `⟨b, rfl⟩` from `(hf w).1 hw`. Take `⟨a, e, rfl⟩` from `hs b`. Use `⟨s • a, Submodule.smul_mem_smul hs' Submodule.mem_top, f (s • m • e), (hf _).2 ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, ← map_nsmul, ← map_add, ← map_smul, map_smul t, smul_add, hm, mul_smul, smul_comm s l.M]`.

Introduce and unpack `x y ⟨a, ha, u, hu, rfl⟩ ⟨a', ha', u', hu', rfl⟩`. Use `⟨a + a', add_mem ha ha', u + u', add_mem hu hu', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, smul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem isMark_of {H : Host E} (Dw D : Datum H) (l : Geo.Tor.Level H) (L : Lt E r)
    (f : D.La →ₗ[𝓞 E] (Fin r → E)) (hinj : Function.Injective f) (hf : ∀ v, v ∈ L ↔ ∃ a, f a = v)
    (t : Dw.La →ₗ[𝓞 E] D.La) (ht : ∀ a, (∃ b, t a = l.M' • b) ↔ ∃ b, a = l.M' • b)
    (hs : ∀ b, ∃ a e, b = t a + l.M' • e) : IsMark l L (f ∘ₗ t) := by
  obtain ⟨m, hm⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hm0 : m ≠ 0 := by
    rintro rfl
    have h3 := l.three_le
    exact Nat.lcm_ne_zero (by omega) l.A_pos.ne' (hm.trans (mul_zero _))
  refine ⟨fun a => (hf _).2 ⟨_, rfl⟩, fun a _ ⟨u, hu, hau⟩ => ?_, fun v hv => ?_⟩
  · obtain ⟨b, rfl⟩ := (hf u).1 hu
    have h1 : t a = l.M • b := hinj (by rw [map_nsmul]; exact hau)
    obtain ⟨b', hb'⟩ := (ht (m • a)).1 ⟨b, by rw [map_nsmul, h1, hm, mul_comm, mul_smul]⟩
    exact ⟨b', nsmul_cancel Dw hm0 (by rw [hb', hm, mul_comm, mul_smul])⟩
  · refine Submodule.smul_induction_on hv (fun s hs' w hw => ?_) ?_
    · obtain ⟨b, rfl⟩ := (hf w).1 hw
      obtain ⟨a, e, rfl⟩ := hs b
      refine ⟨s • a, Submodule.smul_mem_smul hs' Submodule.mem_top, f (s • m • e), (hf _).2 ⟨_, rfl⟩, ?_⟩
      rw [LinearMap.comp_apply, ← map_nsmul, ← map_add, ← map_smul, map_smul t, smul_add, hm, mul_smul,
        smul_comm s l.M]
    · rintro x y ⟨a, ha, u, hu, rfl⟩ ⟨a', ha', u', hu', rfl⟩
      refine ⟨a + a', add_mem ha ha', u + u', add_mem hu hu', ?_⟩
      rw [map_add, smul_add]; abel

end GlobalTheory.Dict.UWLat

open GlobalTheory.Dict.UWLat in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U hσ hU hr W k`. Take `⟨hrank, htype, -⟩` from `hU`. Take `⟨hp0, hty⟩` from `htype k`. Take `⟨hbij, hrt, -, -⟩` from `GlobalTheory.Relab.relab_good E H l c σ hσ`. Take `⟨hp, hq⟩` from `W.F.sig (W.ik k)`.

Establish `hemb : ∀ a, W.emb k a = (W.φ k a : Fin r → E)` using `fun _ => rfl`. Establish `hrange : ∀ v, v ∈ (U.X k).Λ ↔ ∃ a, W.emb k a = v` using `fun v => ⟨fun hv => ⟨(W.φ k).symm ⟨v, hv⟩, by rw [hemb, LinearEquiv.apply_symm_apply]⟩, fun ⟨a, ha⟩ => ha ▸ (W.φ k a).2⟩`. Establish `hinj : Function.Injective (W.emb k)` using `fun a b hab => (W.φ k).injective (Subtype.ext hab)`. Establish `hκ : (U.X k).κ0 = 2 * (U.X k).ξ0`. Use `(U.X k).κ0_xi.resolve_right fun hκ => ?_` and prove the remaining obligations.

Take `⟨x, hx⟩` from `(GlobalTheory.frames_isConnected E r (U.X k)).nonempty`. Take `⟨P, hP, ⟨-, -, -, hspan, A, -, hA, hAE⟩, -⟩` from `W.pt k ⟨x, hx⟩`. Take `⟨f, hf⟩` from `FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hrank (relab c σ) hbij Dw.mult (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))]) (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])`. Set `idx : Fin W.g ≃ (U.X k).Ψ × Fin r` to `W.e.trans f`. Establish `hper : ∀ a, P a = pv (U.X k) idx x (W.emb k a)`.

Introduce `a`. Use function extensionality and compare the values at `j`. Rewrite using `[hP, ← hemb]`. Establish `h` using `hf (W.e j)`. Express the relevant statement in the definitionally equal form `_ = per (U.X k) x (W.emb k a) (f (W.e j))`.

Generalize the expression as in `f (W.e j) = t at h ⊢`. Take `⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩` from `t`. Simplify using `only at h ⊢`. Rewrite `h` using `[← hp0]`. Rewrite using `[per_apply]`.

Simplify using `only`. Break down `h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩` into its components or cases. Rewrite using `[if_neg (by omega)]`. Unfold `perFr`. Rewrite using `[dif_pos a, dif_pos hn]`.

Rewrite using `[if_pos (by omega)]`. Unfold `perFr`. Rewrite using `[dif_neg a, dif_pos (show conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]`. Both sides reduce to the same expression. Take `⟨B, hB, hBE⟩` from `exists_pos_form (U.X k) idx hx`.

Use `haveI : Nonempty (Fin W.g) := by`. Take `⟨τ₀⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : ∃ τ, τ ∈ (U.X k).Ψ := by`. Distinguish the cases in `h : ComplexEmbedding.conjugate τ₀ ∈ (U.X k).Ψ`. Conclude with `⟨_, h⟩`.

Conclude with `⟨τ₀, ((U.X k).cmType τ₀).2 h⟩`. Conclude with `⟨idx.symm (⟨τ, hτ⟩, ⟨0, hr⟩)⟩`. Use `not_opposite P hspan A B hA hB fun a b => ?_` and prove the remaining obligations. Rewrite using `[hAE, hper, hper, hBE]`. Establish `h1` using `W.isom k a b`.

Establish `h2 : EF (U.X k) (W.emb k a) (W.emb k b) = -(((W.F.Di (W.ik k)).EF a b : ℤ) : ℚ)`. Rewrite using `[h1, EF_def, ← map_neg, hκ, hemb, hemb]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`.

Simplify using the standard rewrite rules. Establish `hE : ∀ a b, (((W.F.Di (W.ik k)).EF a b : ℤ) : ℚ) = EF (U.X k) (W.emb k a) (W.emb k b)`. Introduce `a b`. Rewrite using `[W.isom, EF_def, hκ, hemb, hemb]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨hκ, selfD_of_unimod _ _ _ hrange hE, isMark_of Dw _ l _ _ hinj hrange _ (W.F.t_inj _) (W.F.t_surj _), by rw [hp, hq, hrank], hinj, ?_, hE⟩` and prove the remaining obligations. Establish `: Set.range (W.emb k) = ((U.X k).Λ : Set (Fin r → E))`. Use extensionality with `v`. Conclude with `(hrange v).symm`.

Rewrite using `[this]`. Conclude with `(U.X k).Λ_span`.
-/
theorem GlobalTheory.Dict.uw_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (W : UW U) (k : U.Comp), (U.X k).κ0 = 2 * (U.X k).ξ0 ∧ SelfD (U.X k) (U.X k).Λ ∧ IsMark l (U.X k).Λ (W.mark k) ∧ r = (W.F.Di (W.ik k)).p + (W.F.Di (W.ik k)).q ∧ Function.Injective (W.emb k) ∧ Submodule.span E (Set.range (W.emb k)) = ⊤ ∧ ∀ a b, (((W.F.Di (W.ik k)).EF a b : ℤ) : ℚ) = EF (U.X k) (W.emb k a) (W.emb k b) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hr W k
  obtain ⟨hrank, htype, -⟩ := hU
  obtain ⟨hp0, hty⟩ := htype k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp, hq⟩ := W.F.sig (W.ik k)
  have hemb : ∀ a, W.emb k a = (W.φ k a : Fin r → E) := fun _ => rfl
  have hrange : ∀ v, v ∈ (U.X k).Λ ↔ ∃ a, W.emb k a = v := fun v =>
    ⟨fun hv => ⟨(W.φ k).symm ⟨v, hv⟩, by rw [hemb, LinearEquiv.apply_symm_apply]⟩,
      fun ⟨a, ha⟩ => ha ▸ (W.φ k a).2⟩
  have hinj : Function.Injective (W.emb k) := fun a b hab => (W.φ k).injective (Subtype.ext hab)
  have hκ : (U.X k).κ0 = 2 * (U.X k).ξ0 := by
    refine (U.X k).κ0_xi.resolve_right fun hκ => ?_
    obtain ⟨x, hx⟩ := (GlobalTheory.frames_isConnected E r (U.X k)).nonempty
    obtain ⟨P, hP, ⟨-, -, -, hspan, A, -, hA, hAE⟩, -⟩ := W.pt k ⟨x, hx⟩
    obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hrank (relab c σ) hbij
      Dw.mult
      (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
      (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
    let idx : Fin W.g ≃ (U.X k).Ψ × Fin r := W.e.trans f
    have hper : ∀ a, P a = pv (U.X k) idx x (W.emb k a) := by
      intro a
      funext j
      rw [hP, ← hemb]
      have h := hf (W.e j)
      change _ = per (U.X k) x (W.emb k a) (f (W.e j))
      generalize f (W.e j) = t at h ⊢
      obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
      dsimp only at h ⊢
      rw [← hp0] at h
      rw [per_apply]
      dsimp only
      rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
      · rw [if_neg (by omega)]
        unfold perFr
        rw [dif_pos a, dif_pos hn]
      · rw [if_pos (by omega)]
        unfold perFr
        rw [dif_neg a, dif_pos (show conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
        rfl
    obtain ⟨B, hB, hBE⟩ := exists_pos_form (U.X k) idx hx
    haveI : Nonempty (Fin W.g) := by
      obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
      obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ (U.X k).Ψ := by
        by_cases h : ComplexEmbedding.conjugate τ₀ ∈ (U.X k).Ψ
        · exact ⟨_, h⟩
        · exact ⟨τ₀, ((U.X k).cmType τ₀).2 h⟩
      exact ⟨idx.symm (⟨τ, hτ⟩, ⟨0, hr⟩)⟩
    refine not_opposite P hspan A B hA hB fun a b => ?_
    rw [hAE, hper, hper, hBE]
    have h1 := W.isom k a b
    have h2 : EF (U.X k) (W.emb k a) (W.emb k b) = -(((W.F.Di (W.ik k)).EF a b : ℤ) : ℚ) := by
      rw [h1, EF_def, ← map_neg, hκ, hemb, hemb]
      congr 1; ring
    rw [h2]; simp
  have hE : ∀ a b, (((W.F.Di (W.ik k)).EF a b : ℤ) : ℚ) = EF (U.X k) (W.emb k a) (W.emb k b) := by
    intro a b
    rw [W.isom, EF_def, hκ, hemb, hemb]
    congr 1; ring
  refine ⟨hκ, selfD_of_unimod _ _ _ hrange hE,
    isMark_of Dw _ l _ _ hinj hrange _ (W.F.t_inj _) (W.F.t_surj _), by rw [hp, hq, hrank], hinj, ?_, hE⟩
  have : Set.range (W.emb k) = ((U.X k).Λ : Set (Fin r → E)) := by
    ext v; exact (hrange v).symm
  rw [this]; exact (U.X k).Λ_span
