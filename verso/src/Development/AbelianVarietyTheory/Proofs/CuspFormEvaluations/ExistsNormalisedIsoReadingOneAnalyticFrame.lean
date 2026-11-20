import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AbelianHolomorphicFrameReadingConstOfFormsCancelStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GeneratorReadingCorrMulInvStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GeneratorReadingPullbackPeriodRigidStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal.PrimRd

/- English proof (translation)
Use `revert I`. Evaluate the decidable proposition.
-/
theorem finset_fin_two_eq_cases (I : Finset (Fin 2)) : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  revert I
  decide

/- English proof (translation)
Take `⟨I⟩` from `I`. Establish `h0 : Φ.e 0 = 1` using `(Φ.e_ker 0).2 (zero_mem _)`. Break down `finset_fin_two_eq_cases I with rfl | rfl | rfl | rfl` into its components or cases. Use `show Φ.e z ≫ (toUnit A ≫ η) = _`. Simplify using `[psumL, h0]`.

Both sides reduce to the same expression. Use `show Φ.e z ≫ (lift (𝟙 A) (toUnit A ≫ η) ≫ μ) = _`. Simplify using `[psumL]`. Use `show Φ.e z ≫ (lift w (toUnit A ≫ η) ≫ μ) = _`. Simplify using `[psumL]`.

Conclude with `h.symm`. Use `show Φ.e z ≫ (lift (𝟙 A) (lift w (toUnit A ≫ η) ≫ μ) ≫ μ) = _`. Simplify using `[psumL, Φ.e_add, h]`. Rewrite using `[← Category.assoc, comp_lift, Category.comp_id]`. Both sides reduce to the same expression.
-/
theorem e_psum {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) (w : A ⟶ A) (z z' : Fin g → ℂ) (h : Φ.e z' = Φ.e z ≫ w) (I : ULift.{0} (Finset (Fin 2))) :
    Φ.e z ≫ psum A ![𝟙 A, w] I.down = Φ.e (psumL 2 g I ![z, z']) := by
  obtain ⟨I⟩ := I
  have h0 : Φ.e 0 = 1 := (Φ.e_ker 0).2 (zero_mem _)
  rcases finset_fin_two_eq_cases I with rfl | rfl | rfl | rfl
  · show Φ.e z ≫ (toUnit A ≫ η) = _
    simp [psumL, h0]
    rfl
  · show Φ.e z ≫ (lift (𝟙 A) (toUnit A ≫ η) ≫ μ) = _
    simp [psumL]
  · show Φ.e z ≫ (lift w (toUnit A ≫ η) ≫ μ) = _
    simp [psumL]
    exact h.symm
  · show Φ.e z ≫ (lift (𝟙 A) (lift w (toUnit A ≫ η) ≫ μ) ≫ μ) = _
    simp [psumL, Φ.e_add, h]
    rw [← Category.assoc, comp_lift, Category.comp_id]
    rfl

/- English proof (translation)
Rewrite using `[Fintype.sum_equiv Equiv.ulift f (fun x => f ⟨x⟩) (fun _ => rfl)]`. Establish `hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}}` using `by decide`. Rewrite using `[hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]`. Simplify using `only [add_assoc]`.
-/
theorem sum_ulift_finset_fin_two_expand {M : Type} [AddCommMonoid M] (f : ULift.{0} (Finset (Fin 2)) → M) :
    ∑ I, f I = f ⟨∅⟩ + f ⟨{0}⟩ + f ⟨{1}⟩ + f ⟨{0, 1}⟩ := by
  rw [Fintype.sum_equiv Equiv.ulift f (fun x => f ⟨x⟩) (fun _ => rfl)]
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [add_assoc]

/- English proof (translation)
Introduce `ψ`. Distinguish the cases in `hψ : f = ψ`. Substitute `hψ` using the available equality. Simplify `hs` using `[h, h']`. Simplify using `[h, h', hψ]`.
-/
theorem sameSum_of_const {X Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (f : Y ⟶ X) (h : ∀ k, φ k = f) (h' : ∀ k, φ' k = f)
    (hs : ∑ k, ε k = ∑ k, ε' k) : LB.SameSum φ ε φ' ε' := by
  intro ψ
  by_cases hψ : f = ψ
  · subst hψ
    simpa [h, h'] using hs
  · simp [h, h', hψ]

/- English proof (translation)
Establish `hrt : H.bar H.rt = -H.rt`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[H.bar_eq]`. Use `push_cast`. Use `set r : E := (H.rt : E) with hr`.

Establish `hr2 : r ^ 2 = -(H.d : E)`. Use `congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq` as an intermediate fact. Simplify `this` using `[hr]`. Establish `hc2 : (IsCMField.complexConj E r) ^ 2 = r ^ 2`. Rewrite using `[← map_pow, hr2]`.

Simplify using the standard rewrite rules. Establish `hprod : (IsCMField.complexConj E r - r) * (IsCMField.complexConj E r + r) = 0`. Take the linear combination `hc2`. Break down `mul_eq_zero.1 hprod with h1 | h1` into its components or cases. It suffices to derive a contradiction.

Establish `heq : IsCMField.complexConj E r = r` using `sub_eq_zero.1 h1`. Set `τ : E →+* ℂ` to `(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom`. Establish `h3` using `IsCMField.complexEmbedding_complexConj E τ r`. Rewrite `h3` using `[heq]`. Establish `him : (τ r).im = 0`.

Use `congrArg Complex.im h3` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : (τ r) ^ 2 = -(H.d : ℂ)`. Rewrite using `[← map_pow, hr2]`.

Simplify using the standard rewrite rules. Establish `h5 : τ r = ((τ r).re : ℂ)` using `Complex.ext (by simp) (by simp [him])`. Rewrite `h4` using `[h5]`. Establish `h6 : (τ r).re ^ 2 = -(H.d : ℝ)` using `by exact_mod_cast h4`. Establish `h7 : (2 : ℝ) ≤ H.d` using `by exact_mod_cast H.d_prime.two_le`.

Use polynomial arithmetic with `[sq_nonneg (τ r).re]`. Conclude with `eq_neg_of_add_eq_zero_left h1`. Establish `hb : H.bar (2 * H.w0) = H.bar (1 + H.rt)` using `by rw [H.two_weight_eq_one_add_root]`. Rewrite `hb` using `[map_mul, map_add, map_one, hrt, map_ofNat]`. Establish `h2 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1`.

Take the linear combination `H.two_weight_eq_one_add_root + hb`. Conclude with `mul_left_cancel₀ two_ne_zero h2`.
-/
private theorem w0_add_bar_w0_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have hrt : H.bar H.rt = -H.rt := by
    apply RingOfIntegers.ext
    rw [H.bar_eq]
    push_cast
    set r : E := (H.rt : E) with hr
    have hr2 : r ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa [hr] using this
    have hc2 : (IsCMField.complexConj E r) ^ 2 = r ^ 2 := by
      rw [← map_pow, hr2]
      simp
    have hprod : (IsCMField.complexConj E r - r) * (IsCMField.complexConj E r + r) = 0 := by
      linear_combination hc2
    rcases mul_eq_zero.1 hprod with h1 | h1
    · exfalso
      have heq : IsCMField.complexConj E r = r := sub_eq_zero.1 h1
      let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
      have h3 := IsCMField.complexEmbedding_complexConj E τ r
      rw [heq] at h3
      have him : (τ r).im = 0 := by
        have := congrArg Complex.im h3
        simp at this
        linarith
      have h4 : (τ r) ^ 2 = -(H.d : ℂ) := by
        rw [← map_pow, hr2]
        simp
      have h5 : τ r = ((τ r).re : ℂ) := Complex.ext (by simp) (by simp [him])
      rw [h5] at h4
      have h6 : (τ r).re ^ 2 = -(H.d : ℝ) := by exact_mod_cast h4
      have h7 : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
      nlinarith [sq_nonneg (τ r).re]
    · exact eq_neg_of_add_eq_zero_left h1
  have hb : H.bar (2 * H.w0) = H.bar (1 + H.rt) := by rw [H.two_weight_eq_one_add_root]
  rw [map_mul, map_add, map_one, hrt, map_ofNat] at hb
  have h2 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    linear_combination H.two_weight_eq_one_add_root + hb
  exact mul_left_cancel₀ two_ne_zero h2

/- English proof (translation)
Establish `hB1 : ∀ a b c, hermForm Hm (a + b) c = hermForm Hm a c + hermForm Hm b c`. Introduce `a b c`. Simplify using `[hermForm, add_dotProduct]`. Establish `hB2 : ∀ a b c, hermForm Hm a (b + c) = hermForm Hm a b + hermForm Hm a c`. Introduce `a b c`.

Simplify using `[hermForm, Matrix.mulVec_add, dotProduct_add]`. Establish `hB0 : ∀ a, hermForm Hm 0 a = 0` using `by intro a; simp [hermForm]`. Rewrite using `[Fintype.sum_sum_type, sum_ulift_finset_fin_two_expand, Fin.sum_univ_one]`. Simplify using `[psumL, cε, hB1, hB2, hB0]`. Establish `k3 : hermForm Hm z w = hermForm Hm z (T w) + hermForm Hm z (Tb w)` using `by rw [← hB2, hTT]`.

Rewrite using `[hadj z w]`. Take the linear combination `k3`.
-/
private theorem hf_eq_cj_hf_swap_of_isHerm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (T Tb : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hadj : ∀ z w, hermForm Hm (T z) w = hermForm Hm z (Tb w)) (hTT : ∀ w, T w + Tb w = w) (z w : Fin g → ℂ) :
    ∑ k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)), (((Sum.elim (fun _ => (1 : ℤ)) fun I => -cε 2 I) k : ℤ) : ℂ) *
      hermForm Hm ((Sum.elim (fun _ => LinearMap.id) (fun I => (psumL 2 g I).comp (LinearMap.pi ![LinearMap.id, T])) :
        (Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k z)
        ((Sum.elim (fun _ => LinearMap.id) (fun I => (psumL 2 g I).comp (LinearMap.pi ![LinearMap.id, T])) :
        (Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k w) = 0 := by
  have hB1 : ∀ a b c, hermForm Hm (a + b) c = hermForm Hm a c + hermForm Hm b c := by
    intro a b c
    simp [hermForm, add_dotProduct]
  have hB2 : ∀ a b c, hermForm Hm a (b + c) = hermForm Hm a b + hermForm Hm a c := by
    intro a b c
    simp [hermForm, Matrix.mulVec_add, dotProduct_add]
  have hB0 : ∀ a, hermForm Hm 0 a = 0 := by intro a; simp [hermForm]
  rw [Fintype.sum_sum_type, sum_ulift_finset_fin_two_expand, Fin.sum_univ_one]
  simp [psumL, cε, hB1, hB2, hB0]
  have k3 : hermForm Hm z w = hermForm Hm z (T w) + hermForm Hm z (Tb w) := by rw [← hB2, hTT]
  rw [hadj z w]
  linear_combination k3

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ y g ty el Φ`. Establish `hw0 : IsMonHom (Xo.univ.t.act.act H.w0)` using `Xo.univ.t.act.hom H.w0`. Establish `hη : η ≫ Xo.univ.t.act.act H.w0 = η` using `IsMonHom.one_hom _`. Use `⟨Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.exists_wP Xo.univ.t, ?_⟩` and prove the remaining obligations. Introduce `wP hP z`.

Take `⟨hPg, hPc⟩` from `hP`. Set `Λ : (Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)` to `Sum.elim (fun _ => LinearMap.id) (fun I => (psumL 2 g I).comp (LinearMap.pi ![LinearMap.id, tyAct ty H.w0]))`. Establish `hΛl : ∀ k z, Λ (Sum.inl k) z = z` using `fun _ _ => rfl`. Establish `hΛr : ∀ I z, Λ (Sum.inr I) z = psumL 2 g I ![z, tyAct ty H.w0 z]`. Introduce `I z`.

Simplify using `only [Λ, Sum.elim_inr, LinearMap.comp_apply]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`. Establish `hlin : ∀ z, Φ.e (tyAct ty H.w0 z) = Φ.e z ≫ Xo.univ.t.act.act H.w0` using `Φ.lin H.w0`.

Establish `h0 : Φ.e 0 = 1` using `(Φ.e_ker 0).2 (zero_mem _)`. Establish `hφ : ∀ z k, (Φ.e z).left ≫ (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])) k = (Φ.e (Λ k z)).left`. Introduce `z k`. Break down `k with k | I` into its components or cases. Simplify using `[hΛl]`.

Use `e_psum Φ.toAnFr (Xo.univ.t.act.act H.w0) z (tyAct ty H.w0 z) (hlin z) I` as an intermediate fact. Rewrite using `[hΛr, ← this]`. Both sides reduce to the same expression. Establish `hT : ∀ gm ∈ Φ.lat, tyAct ty H.w0 gm ∈ Φ.lat`. Introduce `gm hgm`.

Apply `(Φ.e_ker _).1` to reduce the goal to its premises. Rewrite using `[hlin, (Φ.e_ker gm).2 hgm]`. Use `show (toUnit _ ≫ η) ≫ _ = toUnit _ ≫ η`. Rewrite using `[Category.assoc, hη]`. Establish `p0 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨∅⟩ ![a, b] = 0` using `by intro a b; simp [psumL]`.

Establish `p1 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨{0}⟩ ![a, b] = a` using `by intro a b; simp [psumL]`. Establish `p2 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨{1}⟩ ![a, b] = b` using `by intro a b; simp [psumL]`. Establish `p3 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨{0, 1}⟩ ![a, b] = a + b` using `by intro a b; simp [psumL]`. Establish `hper : ∀ gm ∈ Φ.lat, (∀ z, (Φ.e (z + gm)).left = (Φ.e z).left) ∧ ∀ k, Λ k gm ∈ Φ.lat`. Introduce `gm hgm`.

Use `⟨fun z => by rw [Φ.e_add, (Φ.e_ker gm).2 hgm, _root_.mul_one], fun k => ?_⟩` and prove the remaining obligations. Break down `k with k | I` into its components or cases. Conclude with `hgm`. Rewrite using `[hΛr]`. Take `⟨I⟩` from `I`.

Break down `finset_fin_two_eq_cases I with rfl | rfl | rfl | rfl` into its components or cases. Rewrite using `[p0]`. Conclude with `zero_mem _`. Rewrite using `[p1]`. Conclude with `hgm`.

Rewrite using `[p2]`. Conclude with `hT gm hgm`. Rewrite using `[p3]`. Conclude with `add_mem hgm (hT gm hgm)`. Establish `hbar` using `w0_add_bar_w0_eq_one H`.

Establish `hTT : ∀ w, tyAct ty H.w0 w + tyAct ty (H.bar H.w0) w = w`. Introduce `w`. Use function extensionality and compare the values at `k`. Establish `h1 : ((H.w0 : E) + (H.bar H.w0 : E)) = 1`. Conclude with `congrArg (fun x : 𝓞 E => (x : E)) hbar` after adjusting the coercions.

Simplify using `only [tyAct, Pi.add_apply, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]`. Rewrite using `[← add_mul, ← map_add, h1, map_one, _root_.one_mul]`. Establish `hherm : ∀ z w, ∑ k, (((Sum.elim (fun _ => (1 : ℤ)) fun I => -cε 2 I) k : ℤ) : ℂ) * hermForm Φ.Hm (Λ k z) (Λ k w) = 0` using `fun z w => hf_eq_cj_hf_swap_of_isHerm Φ.Hm (tyAct ty H.w0) (tyAct ty (H.bar H.w0)) (Φ.adj H.w0) hTT z w`. Take `⟨⟨v, hv0, hv⟩, -⟩` from `GlobalTheory.T.abelianHolomorphicFrame_reading_const_of_forms_cancel _ _ _ _ g Φ.toAnFr _ _ (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])) (Sum.elim (fun _ => 1) fun I => -cε 2 I) wP hPg g (fun z => (Φ.e z).left) Λ Φ.lat Φ.hol hφ Φ.span hpe …`. Establish `heS : ∀ k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)), eSec Xo.univ.t.G ≫ (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])) k = eSec Xo.univ.t.G`.

Introduce `k`. Break down `k with k | I` into its components or cases. Simplify using the standard rewrite rules. Take `⟨I⟩` from `I show (η ≫ psum Xo.univ.t.G ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0] I).left = (η : _ ⟶ Xo.univ.t.G).left`. Use `congr 1`.

Break down `finset_fin_two_eq_cases I with rfl | rfl | rfl | rfl` into its components or cases. Use `show η ≫ (toUnit _ ≫ η) = η`. Simplify using the standard rewrite rules. Use `show η ≫ (lift (𝟙 _) (toUnit _ ≫ η) ≫ μ) = η`. Simplify using the standard rewrite rules.

Use `show η ≫ (lift (Xo.univ.t.act.act H.w0) (toUnit _ ≫ η) ≫ μ) = η`. Simplify using `[hη]`. Use `show η ≫ (lift (𝟙 _) (lift (Xo.univ.t.act.act H.w0) (toUnit _ ≫ η) ≫ μ) ≫ μ) = η`. Simplify using the standard rewrite rules. Establish `hv1 : v = 1`.

Establish `A0` using `hv 0`. Establish `hz : ∀ k, Λ k 0 = 0` using `fun k => map_zero _`. Establish `hq0 : (Φ.e 0).left = y.x ≫ eSec Xo.univ.t.G`. Rewrite using `[h0]`. Both sides reduce to the same expression.

Simplify using `only [hz, hq0] at A0`. Establish `A2` using `((GlobalTheory.T.generatorReading_pullback_period_rigid _ _ _ _ g Φ.toAnFr _ _ _ _ wP).1 _ (eSec Xo.univ.t.G) y.x _ v).2 A0`. Establish `A3 : Φ.toAnFr.GenRd (fun _ : PUnit => eSec Xo.univ.t.G) (fun _ => 1) Xo.univ.t.PP.rig y.x (fun _ => 0) 1`. Take `⟨b1, b2⟩` from `(GlobalTheory.T.generatorReading_pullback_period_rigid _ _ _ _ g Φ.toAnFr _ _ (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])) (Sum.elim (fun _ => 1) fun I => -cε 2 I) wP).2.2 1`. Use `⟨b1, fun j hj => ?_⟩` and prove the remaining obligations.

Establish `b3` using `b2 j hj`. Simplify `b3` using `[rigPow]`. Establish `hsame : LB.SameSum (fun k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)) => eSec Xo.univ.t.G ≫ (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])) k) (Sum.elim (fun _ => 1) fun I => -cε 2 I) (fun _ : PUnit => eSec Xo.univ.t.G) (fun _ => 1)`. Use `sameSum_of_const (eSec Xo.univ.t.G) heS (fun _ => rfl) ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_sum_type, sum_ulift_finset_fin_two_expand, Fin.sum_univ_one]`.

Simplify using `[cε]`. Conclude with `(GlobalTheory.T.generatorReading_corr_mul_inv _ _ _ _ g Φ.toAnFr _ _ _ _ _ _ _ _ _ y.x _ _ v 1 A2 A3).2.1 hPc hsame ⟨fun _ => 0, fun _ => rfl, fun _ => rfl⟩`. Establish `hfin` using `hv z`. Rewrite `hfin` using `[hv1]`. Establish `hpt : (fun k => Λ k z) = Sum.elim (fun _ => z) (fun I => psumL 2 g I ![z, tyAct ty H.w0 z])`.

Use function extensionality and compare the values at `k`. Break down `k with k | I` into its components or cases. Both sides reduce to the same expression. Conclude with `hΛr I z`. Rewrite `hfin` using `[hpt]`.

Conclude with `hfin`.
-/
theorem prim_reading : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), (∃ wP : PrimTy H Xo, IsPrim wP) ∧ ∀ wP : PrimTy H Xo, IsPrim wP → ∀ z : Fin g → ℂ, Φ.toAnFr.GenRd _ _ wP (Φ.e z).left (Sum.elim (fun _ => z) (fun I => psumL 2 g I ![z, tyAct ty H.w0 z])) 1 := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ
  have hw0 : IsMonHom (Xo.univ.t.act.act H.w0) := Xo.univ.t.act.hom H.w0
  have hη : η ≫ Xo.univ.t.act.act H.w0 = η := IsMonHom.one_hom _
  refine ⟨Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.exists_wP Xo.univ.t, ?_⟩
  intro wP hP z
  obtain ⟨hPg, hPc⟩ := hP
  let Λ : (Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    Sum.elim (fun _ => LinearMap.id)
      (fun I => (psumL 2 g I).comp (LinearMap.pi ![LinearMap.id, tyAct ty H.w0]))
  have hΛl : ∀ k z, Λ (Sum.inl k) z = z := fun _ _ => rfl
  have hΛr : ∀ I z, Λ (Sum.inr I) z = psumL 2 g I ![z, tyAct ty H.w0 z] := by
    intro I z
    simp only [Λ, Sum.elim_inr, LinearMap.comp_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hlin : ∀ z, Φ.e (tyAct ty H.w0 z) = Φ.e z ≫ Xo.univ.t.act.act H.w0 := Φ.lin H.w0
  have h0 : Φ.e 0 = 1 := (Φ.e_ker 0).2 (zero_mem _)
  have hφ : ∀ z k, (Φ.e z).left ≫
      (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])) k =
      (Φ.e (Λ k z)).left := by
    intro z k
    rcases k with k | I
    · simp [hΛl]
    · have := e_psum Φ.toAnFr (Xo.univ.t.act.act H.w0) z (tyAct ty H.w0 z) (hlin z) I
      rw [hΛr, ← this]
      rfl
  have hT : ∀ gm ∈ Φ.lat, tyAct ty H.w0 gm ∈ Φ.lat := by
    intro gm hgm
    apply (Φ.e_ker _).1
    rw [hlin, (Φ.e_ker gm).2 hgm]
    show (toUnit _ ≫ η) ≫ _ = toUnit _ ≫ η
    rw [Category.assoc, hη]
  have p0 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨∅⟩ ![a, b] = 0 := by intro a b; simp [psumL]
  have p1 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨{0}⟩ ![a, b] = a := by intro a b; simp [psumL]
  have p2 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨{1}⟩ ![a, b] = b := by intro a b; simp [psumL]
  have p3 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨{0, 1}⟩ ![a, b] = a + b := by intro a b; simp [psumL]
  have hper : ∀ gm ∈ Φ.lat, (∀ z, (Φ.e (z + gm)).left = (Φ.e z).left) ∧ ∀ k, Λ k gm ∈ Φ.lat := by
    intro gm hgm
    refine ⟨fun z => by rw [Φ.e_add, (Φ.e_ker gm).2 hgm, _root_.mul_one], fun k => ?_⟩
    rcases k with k | I
    · exact hgm
    · rw [hΛr]
      obtain ⟨I⟩ := I
      rcases finset_fin_two_eq_cases I with rfl | rfl | rfl | rfl
      · rw [p0]
        exact zero_mem _
      · rw [p1]
        exact hgm
      · rw [p2]
        exact hT gm hgm
      · rw [p3]
        exact add_mem hgm (hT gm hgm)
  have hbar := w0_add_bar_w0_eq_one H
  have hTT : ∀ w, tyAct ty H.w0 w + tyAct ty (H.bar H.w0) w = w := by
    intro w
    funext k
    have h1 : ((H.w0 : E) + (H.bar H.w0 : E)) = 1 := by
      exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) hbar
    simp only [tyAct, Pi.add_apply, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    rw [← add_mul, ← map_add, h1, map_one, _root_.one_mul]
  have hherm : ∀ z w, ∑ k, (((Sum.elim (fun _ => (1 : ℤ)) fun I => -cε 2 I) k : ℤ) : ℂ) *
      hermForm Φ.Hm (Λ k z) (Λ k w) = 0 :=
    fun z w => hf_eq_cj_hf_swap_of_isHerm Φ.Hm (tyAct ty H.w0) (tyAct ty (H.bar H.w0)) (Φ.adj H.w0) hTT z w
  obtain ⟨⟨v, hv0, hv⟩, -⟩ := GlobalTheory.T.abelianHolomorphicFrame_reading_const_of_forms_cancel _ _ _ _ g Φ.toAnFr _ _
    (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0]))
    (Sum.elim (fun _ => 1) fun I => -cε 2 I) wP hPg g (fun z => (Φ.e z).left) Λ Φ.lat Φ.hol hφ Φ.span hper hherm
  have heS : ∀ k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)), eSec Xo.univ.t.G ≫
      (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])) k =
      eSec Xo.univ.t.G := by
    intro k
    rcases k with k | I
    · simp
    · obtain ⟨I⟩ := I
      show (η ≫ psum Xo.univ.t.G ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0] I).left = (η : _ ⟶ Xo.univ.t.G).left
      congr 1
      rcases finset_fin_two_eq_cases I with rfl | rfl | rfl | rfl
      · show η ≫ (toUnit _ ≫ η) = η
        simp
      · show η ≫ (lift (𝟙 _) (toUnit _ ≫ η) ≫ μ) = η
        simp
      · show η ≫ (lift (Xo.univ.t.act.act H.w0) (toUnit _ ≫ η) ≫ μ) = η
        simp [hη]
      · show η ≫ (lift (𝟙 _) (lift (Xo.univ.t.act.act H.w0) (toUnit _ ≫ η) ≫ μ) ≫ μ) = η
        simp
  have hv1 : v = 1 := by
    have A0 := hv 0
    have hz : ∀ k, Λ k 0 = 0 := fun k => map_zero _
    have hq0 : (Φ.e 0).left = y.x ≫ eSec Xo.univ.t.G := by
      rw [h0]
      rfl
    simp only [hz, hq0] at A0
    have A2 := ((GlobalTheory.T.generatorReading_pullback_period_rigid _ _ _ _ g Φ.toAnFr _ _ _ _ wP).1 _ (eSec Xo.univ.t.G) y.x _ v).2 A0
    have A3 : Φ.toAnFr.GenRd (fun _ : PUnit => eSec Xo.univ.t.G) (fun _ => 1) Xo.univ.t.PP.rig y.x (fun _ => 0) 1 := by
      obtain ⟨b1, b2⟩ := (GlobalTheory.T.generatorReading_pullback_period_rigid _ _ _ _ g Φ.toAnFr _ _
        (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0]))
        (Sum.elim (fun _ => 1) fun I => -cε 2 I) wP).2.2 1
      refine ⟨b1, fun j hj => ?_⟩
      have b3 := b2 j hj
      simpa [rigPow] using b3
    have hsame : LB.SameSum (fun k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)) => eSec Xo.univ.t.G ≫
        (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])) k)
        (Sum.elim (fun _ => 1) fun I => -cε 2 I) (fun _ : PUnit => eSec Xo.univ.t.G) (fun _ => 1) := by
      refine sameSum_of_const (eSec Xo.univ.t.G) heS (fun _ => rfl) ?_
      rw [Fintype.sum_sum_type, sum_ulift_finset_fin_two_expand, Fin.sum_univ_one]
      simp [cε]
    exact (GlobalTheory.T.generatorReading_corr_mul_inv _ _ _ _ g Φ.toAnFr _ _ _ _ _ _ _ _ _ y.x _ _ v 1 A2 A3).2.1 hPc hsame
      ⟨fun _ => 0, fun _ => rfl, fun _ => rfl⟩
  have hfin := hv z
  rw [hv1] at hfin
  have hpt : (fun k => Λ k z) = Sum.elim (fun _ => z) (fun I => psumL 2 g I ![z, tyAct ty H.w0 z]) := by
    funext k
    rcases k with k | I
    · rfl
    · exact hΛr I z
  rw [hpt] at hfin
  exact hfin

end GlobalTheory.AnVal.PrimRd
