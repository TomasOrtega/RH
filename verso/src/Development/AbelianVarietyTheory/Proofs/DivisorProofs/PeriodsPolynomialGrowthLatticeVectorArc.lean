import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcLiftPeriodsTendstoSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousPeriodBasisAlongArcStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.PerPoly

open scoped CategoryTheory.MonObj in

/- English proof (translation)
Substitute `hy hy0` using the available equality. Set `ex' : (Fin g → ℂ) → (Over.mk q ⟶ G')` to `fun z => Over.homMk (h0.1.lift (ex0 z).left q (Over.w (ex0 z))) (h0.1.lift_snd _ _ _)`. Establish `e0 : ∀ z, pushHom h0 (Over.mk q) (ex' z) = ex0 z` using `fun z => Over.OverMorphism.ext (h0.1.lift_fst _ _ _)`. Establish `e0' : ∀ z, (ex' z).left ≫ φ0 = (ex0 z).left` using `fun z => h0.1.lift_fst _ _ _`. Establish `e1 : ∀ z, (ex' z).left ≫ G'.hom = q` using `fun z => Over.w (ex' z)`.

Establish `inj0 : Function.Injective (pushHom h0 (Over.mk q))` using `fun a b hab => Over.OverMorphism.ext (h0.1.hom_ext (congrArg (·.left) hab) ((Over.w a).trans (Over.w b).symm))`. Establish `inj : Function.Injective (pushHom h (Over.mk q))` using `fun a b hab => Over.OverMorphism.ext (h.1.hom_ext (congrArg (·.left) hab) ((Over.w a).trans (Over.w b).symm))`. Establish `hA : ∀ t, HolHom.HolAt (fun z => (show Sp ℂ ⟶ G'.left from (ex' z).left)) t` using `fun t => HolHom.holAt_of_isPullback h0.1 (by simp only [e0']; exact HolHom.holAt_of_isHolTo hol (Set.mem_univ t)) (by simp only [e1]; exact HolHom.holAt_const _ _)`. Use `⟨fun z => pushHom h (Over.mk q) (ex' z), fun z w => ?_, ?_, fun d w hw hd => ?_, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩` and prove the remaining obligations. Establish `: ex' (z + w) = ex' z * ex' w` using `inj0 (by rw [map_mul, e0, e0, e0]; exact hadd z w)`.

Conclude with `(congrArg _ this).trans (map_mul _ _ _)`. Conclude with `HolHom.isHolTo_of_holAt isOpen_univ fun t _ => (hA t).comp φ`. Take `⟨v, hv⟩` from `(hA 0).exists_isDerivAt d`. Establish `h1` using `hv.comp φ0`. Simplify using `only [e0'] at h1`.

Establish `h2 : v = w` using `h0.1.hom_ext (h1.unique ((HolHom.isDerivAt0_iff _ _ _).1 hd)) ((HolHom.IsDerivAt.over (a := ex') hv).trans hw.symm)`. Substitute `h2` using the available equality. Conclude with `(HolHom.isDerivAt0_iff _ _ _).2 (hv.comp φ)`. Establish `: ex' z = 1` using `inj (hz.trans (map_one _).symm)`. Rewrite using `[← e0, this]`.

Conclude with `map_one _`. Establish `: ex' z = 1` using `inj0 ((e0 z).trans (hz.trans (map_one _).symm)) show pushHom h (Over.mk q) (ex' z) = 1`. Rewrite using `[this]`. Conclude with `map_one _`.
-/
theorem exists_transfer_iff {S S' S0 : Scheme.{0}} {G : Over S} {G' : Over S'} {G0 : Over S0} [GrpObj G] [GrpObj G']
    [GrpObj G0] {f : S' ⟶ S} {f0 : S' ⟶ S0} {φ : G'.left ⟶ G.left} {φ0 : G'.left ⟶ G0.left}
    (h : IsGrpPullback G' G f φ) (h0 : IsGrpPullback G' G0 f0 φ0) (q : Sp ℂ ⟶ S') {y : Sp ℂ ⟶ S} {y0 : Sp ℂ ⟶ S0}
    (hy : q ≫ f = y) (hy0 : q ≫ f0 = y0) {g : ℕ} (ex0 : (Fin g → ℂ) → (Over.mk y0 ⟶ G0))
    (hadd : ∀ z w, ex0 (z + w) = ex0 z * ex0 w)
    (hol : IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G0.left from (ex0 z).left))) :
    ∃ ex : (Fin g → ℂ) → (Over.mk y ⟶ G), (∀ z w, ex (z + w) = ex z * ex w) ∧
      IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (ex z).left)) ∧
      (∀ (d : Fin g → ℂ) (w : Sp (DualNumber ℂ) ⟶ G'.left),
        w ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ q →
        IsDerivAt0 (fun z => (ex0 z).left) d (w ≫ φ0) → IsDerivAt0 (fun z => (ex z).left) d (w ≫ φ)) ∧
      ∀ z, ex z = 1 ↔ ex0 z = 1 := by
  subst hy hy0
  let ex' : (Fin g → ℂ) → (Over.mk q ⟶ G') := fun z =>
    Over.homMk (h0.1.lift (ex0 z).left q (Over.w (ex0 z))) (h0.1.lift_snd _ _ _)
  have e0 : ∀ z, pushHom h0 (Over.mk q) (ex' z) = ex0 z := fun z =>
    Over.OverMorphism.ext (h0.1.lift_fst _ _ _)
  have e0' : ∀ z, (ex' z).left ≫ φ0 = (ex0 z).left := fun z => h0.1.lift_fst _ _ _
  have e1 : ∀ z, (ex' z).left ≫ G'.hom = q := fun z => Over.w (ex' z)
  have inj0 : Function.Injective (pushHom h0 (Over.mk q)) := fun a b hab =>
    Over.OverMorphism.ext (h0.1.hom_ext (congrArg (·.left) hab) ((Over.w a).trans (Over.w b).symm))
  have inj : Function.Injective (pushHom h (Over.mk q)) := fun a b hab =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (·.left) hab) ((Over.w a).trans (Over.w b).symm))
  have hA : ∀ t, HolHom.HolAt (fun z => (show Sp ℂ ⟶ G'.left from (ex' z).left)) t := fun t =>
    HolHom.holAt_of_isPullback h0.1
      (by simp only [e0']; exact HolHom.holAt_of_isHolTo hol (Set.mem_univ t))
      (by simp only [e1]; exact HolHom.holAt_const _ _)
  refine ⟨fun z => pushHom h (Over.mk q) (ex' z), fun z w => ?_, ?_, fun d w hw hd => ?_, fun z => ⟨fun hz => ?_,
    fun hz => ?_⟩⟩
  · have : ex' (z + w) = ex' z * ex' w := inj0 (by rw [map_mul, e0, e0, e0]; exact hadd z w)
    exact (congrArg _ this).trans (map_mul _ _ _)
  · exact HolHom.isHolTo_of_holAt isOpen_univ fun t _ => (hA t).comp φ
  · obtain ⟨v, hv⟩ := (hA 0).exists_isDerivAt d
    have h1 := hv.comp φ0
    simp only [e0'] at h1
    have h2 : v = w := h0.1.hom_ext (h1.unique ((HolHom.isDerivAt0_iff _ _ _).1 hd))
      ((HolHom.IsDerivAt.over (a := ex') hv).trans hw.symm)
    subst h2
    exact (HolHom.isDerivAt0_iff _ _ _).2 (hv.comp φ)
  · have : ex' z = 1 := inj (hz.trans (map_one _).symm)
    rw [← e0, this]
    exact map_one _
  · have : ex' z = 1 := inj0 ((e0 z).trans (hz.trans (map_one _).symm))
    show pushHom h (Over.mk q) (ex' z) = 1
    rw [this]
    exact map_one _

def zComb {m : ℕ} {V : Type} [AddCommGroup V] (lam : Fin m → V) : (Fin m → ℤ) →+ V :=
  (Fintype.linearCombination ℤ lam).toAddMonoidHom

/- English proof (translation)
The claim follows from `Fintype.linearCombination_apply ℤ lam n`.
-/
theorem zComb_apply {m : ℕ} {V : Type} [AddCommGroup V] (lam : Fin m → V) (n : Fin m → ℤ) :
    zComb lam n = ∑ j, n j • lam j := Fintype.linearCombination_apply ℤ lam n

/- English proof (translation)
Use `⟨fun n n' h => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[zComb_apply, zComb_apply]`. Establish `h0 : ∑ j, ((n j - n' j : ℤ) : ℝ) • lam j = 0`. Simplify using `only [Int.cast_smul_eq_zsmul, sub_smul, Finset.sum_sub_distrib, h, sub_self]`. Use function extensionality and compare the values at `j`.

Use `Fintype.linearIndependent_iff.1 hli _ h0 j` as an intermediate fact. Conclude with `sub_eq_zero.1 (by exact_mod_cast this)`. Set `bas` to `Module.Basis.mk hli hsp.ge`. Establish `hr : (zComb lam).range = (Submodule.span ℤ (Set.range bas)).toAddSubgroup`. Use extensionality with `x`.

Simplify using `only [bas, AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Module.Basis.coe_mk, Module.Basis.mk_apply, Submodule.mem_span_range_iff_exists_fun, zComb_apply]`. Rewrite using `[hr]`. Conclude with `(inferInstance : DiscreteTopology (Submodule.span ℤ (Set.range bas)))`. Use `eq_top_iff.2 (hsp.ge.trans (Submodule.span_mono ?_))` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`.

Use `⟨Pi.single j 1, ?_⟩` and prove the remaining obligations. Rewrite using `[zComb_apply]`. Simplify using `[Pi.single_apply]`.
-/
theorem zComb_lattice {m g : ℕ} (lam : Fin m → Fin g → ℂ) (hli : LinearIndependent ℝ lam)
    (hsp : Submodule.span ℝ (Set.range lam) = ⊤) :
    Function.Injective (zComb lam) ∧ DiscreteTopology (zComb lam).range ∧
      Submodule.span ℝ (Set.range (zComb lam)) = ⊤ := by
  refine ⟨fun n n' h => ?_, ?_, ?_⟩
  · rw [zComb_apply, zComb_apply] at h
    have h0 : ∑ j, ((n j - n' j : ℤ) : ℝ) • lam j = 0 := by
      simp only [Int.cast_smul_eq_zsmul, sub_smul, Finset.sum_sub_distrib, h, sub_self]
    funext j
    have := Fintype.linearIndependent_iff.1 hli _ h0 j
    exact sub_eq_zero.1 (by exact_mod_cast this)
  · let bas := Module.Basis.mk hli hsp.ge
    have hr : (zComb lam).range = (Submodule.span ℤ (Set.range bas)).toAddSubgroup := by
      ext x
      simp only [bas, AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Module.Basis.coe_mk, Module.Basis.mk_apply,
        Submodule.mem_span_range_iff_exists_fun, zComb_apply]
    rw [hr]
    exact (inferInstance : DiscreteTopology (Submodule.span ℤ (Set.range bas)))
  · refine eq_top_iff.2 (hsp.ge.trans (Submodule.span_mono ?_))
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    rw [zComb_apply]
    simp [Pi.single_apply]

end GlobalTheory.ShFam.PerPoly

namespace GlobalTheory.ShFam.PerPoly

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift v hv R`. Take `⟨hN, hX, -, -, -, g, e, F, ik, φL, -, hfr⟩` from `hU`. Distinguish the cases in `hpq : 1 ≤ Dw.p + Dw.q`. Use `swap`. Use `⟨0, 0, Filter.Eventually.of_forall fun w _ τ i hτ => ?_⟩` and prove the remaining obligations.

It suffices to derive a contradiction. Establish `hp0` using `(hX k).1`. Apply the tactic sequence `rcases hτ with ⟨_, hi⟩ | ⟨_, hi⟩ <;> omega`. Establish `hoff : ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ x) s ∉ genBd Z`. Introduce `u hu hu0 s hb`.

Take `⟨hm1, -⟩` from `hm u hu hu0`. Establish `hm1' : GlobalTheory.AllWt.ptF (y u) ≫ Z.jQ = spMap (ψ u) ≫ x` using `hm1`. Conclude with `hb ⟨GlobalTheory.AllWt.ptF (y u) s, by rw [← hm1']; rfl⟩`. Take `⟨T₀, m, lam, hT₀, hcont, hbas, hker, hgrow⟩` from `GlobalTheory.T.exists_continuous_period_basis_along_arc E H Dw l Xo c O β Z σ A φ x fr ψ r g e hσ hpq harc hoff`. Take `⟨-, -, hxd, hxm, -⟩` from `horb`.

Use `set T₁ := max T T₀ with hT₁def`. Establish `hT₁ : ∀ w : ℂ, T₁ < w.im → T < w.im ∧ T₀ < w.im` using `fun w hw => ⟨(le_max_left _ _).trans_lt hw, (le_max_right _ _).trans_lt hw⟩`. Set `B` to `{w : ℂ // w ∈ {w : ℂ | T₁ < w.im}}`. Use `haveI : PreconnectedSpace B := Subtype.preconnectedSpace (convex_halfSpace_im_gt T₁).isPreconnected`. Establish `hdom : ∀ b : B, xx b ∈ (U.X k).dom` using `fun b => hxm b (hT₁ b b.2).1`.

Use `choose Pm hPm hper hpt hder hrest using fun b : B => hfr k ⟨xx b, hdom b⟩`. Use `clear hrest`. Use `set a₀ := (φL k).symm ⟨v, hv⟩ with ha₀`. Establish `hva : ((φL k a₀ : (U.X k).Λ) : Fin N → E) = v` using `by rw [ha₀, LinearEquiv.apply_symm_apply]`. Establish `key : ∀ b : B, ∃ n : Fin m → ℤ, Pm b a₀ = zComb (lam b) n` using `fun b => by`.

Establish `hb` using `hT₀ b (hT₁ b b.2).2`. Take `⟨_, hx1, hx2⟩` from `hlift b (hT₁ b b.2).1`. Take `⟨hm1, hm2⟩` from `hm _ hb (Complex.exp_ne_zero _)`. Establish `h0 : GlobalTheory.AllWt.ptF (y (eTwoPi b)) ≫ pullback.fst _ _ = (y (eTwoPi b)).x` using `pullback.lift_fst _ _ _`. Take `⟨ex, a1, a2, a3, a4⟩` from `exists_transfer_iff Z.m.cart Z.m0.toSABMap.cart (GlobalTheory.AllWt.ptF (S := CAt σ) (y (eTwoPi b)) :) (y := spMap (ψ (eTwoPi b)) ≫ x ≫ genι Z) (y0 := F.u (ik k) (Pm b)) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ genι Z) hm1).trans (Category.assoc _ _ _))) (h0.trans (hx1. …`.

Establish `hk` using `hker b (hT₁ b b.2).2 ex a1 a2 (fun jj => by`. Take `⟨w, w1, w2, w3⟩` from `hm2 (e jj).1 (e jj).2`. Establish `hd` using `hder b (e jj).1 (e jj).2`. Rewrite `hd` using `[hx2, ← w2, Sigma.eta, Equiv.symm_apply_apply]`. Conclude with `w3 ▸ a3 _ w w1 hd) (Pm b a₀)`.

Take `⟨n, hn⟩` from `hk.1 ((a4 _).2 ((F.ex_ker _ _ (hper b) _).2 ⟨a₀, rfl⟩))`. Conclude with `⟨n, hn.trans (zComb_apply _ _).symm⟩`. Use `choose n hn using key`. Establish `hxc : Continuous fun b : B => xx b` using `(hxd.continuousOn.mono fun w hw => (hT₁ w hw).1).restrict`. Establish `hPc : ∀ z, Continuous fun b : B => Pm b z` using `fun z => continuous_pi fun jj => by`.

Simplify using `only [hPm]`. Conclude with `PerLim.continuous_perFr _ hdom hxc _ _ _`. Establish `hlc : ∀ j, Continuous fun b : B => lam b j` using `fun j => (continuous_apply j).comp (hcont.comp_continuous continuous_subtype_val fun b => (hT₁ b b.2).2)`. Establish `hZc : ∀ z, Continuous fun b : B => zComb (lam b) z` using `fun z => by`. Simplify using `only [zComb_apply]`.

Conclude with `continuous_finset_sum _ fun j _ => (hlc j).const_smul (z j)`. Set `b₀ : B` to `⟨(T₁ + 1 : ℝ) * Complex.I, by simp⟩`. Establish `hconst : ∀ b, n b = n b₀` using `fun b => by`. Use `IsLocallyConstant.apply_eq_of_preconnectedSpace (f := n) ((IsLocallyConstant.iff_eventually_eq _).2 fun b' => ?_) b b₀` and prove the remaining obligations. Take `⟨hi, hd, hs⟩` from `zComb_lattice (lam b') (hbas b' (hT₁ b' b'.2).2).1 (hbas b' (hT₁ b' b'.2).2).2`.

Use `PerLim.eventually_eq_of_lattice (fun b : B => zComb (lam b)) hZc b' hi hd hs n ?_` and prove the remaining obligations. Conclude with `(hPc a₀).congr fun b => hn b`. Take `⟨C, Bx, hC⟩` from `hgrow R`. Establish `hidx : ∀ (τ : E →+* ℂ) (m : ℕ), m = (if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q) → ∃ s : Fin m → Fin g, Function.Injective s ∧ ∀ i, relab c σ (e (s i)).1 = τ ∧ ((e (s i)).2 : ℕ) = i`. Introduce `τ m hmτ`.

Take `⟨τ', rfl⟩` from `Finite.injective_iff_surjective.1 (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_injective c σ) τ`. Establish `h1 : m = Dw.mult τ'`. Rewrite using `[hmτ, Datum.mult]`. Conclude with `if_congr (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_rt c σ hσ τ') rfl rfl`. Substitute `h1` using the available equality.

Use `⟨fun i => e.symm ⟨τ', i⟩, fun i i' h => ?_, fun i => ?_⟩` and prove the remaining obligations. Conclude with `eq_of_heq (Sigma.mk.inj (e.symm.injective h)).2`. Rewrite using `[Equiv.apply_symm_apply]`. Conclude with `⟨rfl, rfl⟩`. Establish `hlet : ∀ (τ : E →+* ℂ) (i : ℕ), (τ ∈ (U.X k).Ψ ∧ i < N - (U.X k).p0) ∨ (conjEmb τ ∈ (U.X k).Ψ ∧ i < (U.X k).p0) → ∃ jj : Fin g, relab c σ (e jj).1 = τ ∧ ((e jj).2 : ℕ) = i`.

Introduce `τ i hτ`. Break down `hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Take `⟨s, -, hs⟩` from `hidx τ (N - (U.X k).p0) (by`. Rewrite using `[if_pos (((hX k).2 _).1 h1), (hX k).1, hN, Nat.add_sub_cancel])`. Conclude with `⟨s ⟨i, h2⟩, hs _⟩`.

Establish `hcc : NumberField.ComplexEmbedding.conjugate (conjEmb τ) = τ` using `RingHom.ext fun a => by`. Simplify using `[conjEmb, NumberField.ComplexEmbedding.conjugate_coe_eq]`. Establish `hne : ¬ τ (H.rt : E) = H.rt0` using `fun h => ((U.X k).cmType (conjEmb τ)).1 h1 (by rw [hcc]; exact ((hX k).2 τ).2 h)`. Take `⟨s, -, hs⟩` from `hidx τ (U.X k).p0 (by rw [if_neg hne, (hX k).1])`. Conclude with `⟨s ⟨i, h2⟩, hs _⟩`.

Use `⟨(∑ j, (|n b₀ j| : ℝ)) * C, Bx, ?_⟩` and prove the remaining obligations. Use `filter_upwards [(tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T₁)] with w hw hR τ i hτ`. Take `⟨jj, hj1, hj2⟩` from `hlet τ i hτ`. Establish `hP : perFr (U.X k) (xx w) v τ i = Pm ⟨w, hw⟩ a₀ jj`. Rewrite using `[hPm, hva, hj1, hj2]`.

Rewrite using `[hP, hn, hconst, zComb_apply]`. Establish `hl` using `hC w (hT₁ w hw).2 hR`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Int.cast_smul_eq_zsmul ℝ, norm_smul, Real.norm_eq_abs, ← Int.cast_abs]`. Conclude with `mul_le_mul_of_nonneg_left (norm_le_pi_norm _ _) (by positivity)`.

Use `_ = (∑ j, (|n b₀ j| : ℝ)) * ‖lam w‖ := (Finset.sum_mul _ _ _).symm`. Use `_ ≤ (∑ j, (|n b₀ j| : ℝ)) * (C * w.im ^ Bx) := mul_le_mul_of_nonneg_left hl (Finset.sum_nonneg fun j _ => by positivity)`. Use `_ = _ := (mul_assoc _ _ _).symm`.
-/
theorem periods_le_of_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∀ v ∈ (U.X k).Λ, ∀ R : ℝ, ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (τ : E →+* ℂ) (i : ℕ), (τ ∈ (U.X k).Ψ ∧ i < N - (U.X k).p0) ∨ (conjEmb τ ∈ (U.X k).Ψ ∧ i < (U.X k).p0) → ‖perFr (U.X k) (xx w) v τ i‖ ≤ C * w.im ^ B := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift v hv R
  obtain ⟨hN, hX, -, -, -, g, e, F, ik, φL, -, hfr⟩ := hU
  by_cases hpq : 1 ≤ Dw.p + Dw.q
  swap
  · refine ⟨0, 0, Filter.Eventually.of_forall fun w _ τ i hτ => ?_⟩
    exfalso
    have hp0 := (hX k).1
    rcases hτ with ⟨_, hi⟩ | ⟨_, hi⟩ <;> omega
  have hoff : ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ x) s ∉ genBd Z := by
    intro u hu hu0 s hb
    obtain ⟨hm1, -⟩ := hm u hu hu0
    have hm1' : GlobalTheory.AllWt.ptF (y u) ≫ Z.jQ = spMap (ψ u) ≫ x := hm1
    exact hb ⟨GlobalTheory.AllWt.ptF (y u) s, by rw [← hm1']; rfl⟩
  obtain ⟨T₀, m, lam, hT₀, hcont, hbas, hker, hgrow⟩ :=
    GlobalTheory.T.exists_continuous_period_basis_along_arc E H Dw l Xo c O β Z σ A φ x fr ψ r g e hσ hpq harc hoff
  obtain ⟨-, -, hxd, hxm, -⟩ := horb
  set T₁ := max T T₀ with hT₁def
  have hT₁ : ∀ w : ℂ, T₁ < w.im → T < w.im ∧ T₀ < w.im := fun w hw =>
    ⟨(le_max_left _ _).trans_lt hw, (le_max_right _ _).trans_lt hw⟩
  let B := {w : ℂ // w ∈ {w : ℂ | T₁ < w.im}}
  haveI : PreconnectedSpace B := Subtype.preconnectedSpace (convex_halfSpace_im_gt T₁).isPreconnected
  have hdom : ∀ b : B, xx b ∈ (U.X k).dom := fun b => hxm b (hT₁ b b.2).1
  choose Pm hPm hper hpt hder hrest using fun b : B => hfr k ⟨xx b, hdom b⟩
  clear hrest
  set a₀ := (φL k).symm ⟨v, hv⟩ with ha₀
  have hva : ((φL k a₀ : (U.X k).Λ) : Fin N → E) = v := by rw [ha₀, LinearEquiv.apply_symm_apply]
  have key : ∀ b : B, ∃ n : Fin m → ℤ, Pm b a₀ = zComb (lam b) n := fun b => by
    have hb := hT₀ b (hT₁ b b.2).2
    obtain ⟨_, hx1, hx2⟩ := hlift b (hT₁ b b.2).1
    obtain ⟨hm1, hm2⟩ := hm _ hb (Complex.exp_ne_zero _)
    have h0 : GlobalTheory.AllWt.ptF (y (eTwoPi b)) ≫ pullback.fst _ _ = (y (eTwoPi b)).x := pullback.lift_fst _ _ _
    obtain ⟨ex, a1, a2, a3, a4⟩ := exists_transfer_iff Z.m.cart Z.m0.toSABMap.cart
      (GlobalTheory.AllWt.ptF (S := CAt σ) (y (eTwoPi b)) :)
      (y := spMap (ψ (eTwoPi b)) ≫ x ≫ genι Z) (y0 := F.u (ik k) (Pm b))
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ genι Z) hm1).trans (Category.assoc _ _ _)))
      (h0.trans (hx1.symm.trans (hpt b))) (F.ex (ik k) (Pm b)) (F.ex_add _ _ (hper b))
      (HolHom.isHolTo_ex F _ (hper b))
    have hk := hker b (hT₁ b b.2).2 ex a1 a2 (fun jj => by
      obtain ⟨w, w1, w2, w3⟩ := hm2 (e jj).1 (e jj).2
      have hd := hder b (e jj).1 (e jj).2
      rw [hx2, ← w2, Sigma.eta, Equiv.symm_apply_apply] at hd
      exact w3 ▸ a3 _ w w1 hd) (Pm b a₀)
    obtain ⟨n, hn⟩ := hk.1 ((a4 _).2 ((F.ex_ker _ _ (hper b) _).2 ⟨a₀, rfl⟩))
    exact ⟨n, hn.trans (zComb_apply _ _).symm⟩
  choose n hn using key
  have hxc : Continuous fun b : B => xx b :=
    (hxd.continuousOn.mono fun w hw => (hT₁ w hw).1).restrict
  have hPc : ∀ z, Continuous fun b : B => Pm b z := fun z => continuous_pi fun jj => by
    simp only [hPm]
    exact PerLim.continuous_perFr _ hdom hxc _ _ _
  have hlc : ∀ j, Continuous fun b : B => lam b j := fun j =>
    (continuous_apply j).comp (hcont.comp_continuous continuous_subtype_val fun b => (hT₁ b b.2).2)
  have hZc : ∀ z, Continuous fun b : B => zComb (lam b) z := fun z => by
    simp only [zComb_apply]
    exact continuous_finset_sum _ fun j _ => (hlc j).const_smul (z j)
  let b₀ : B := ⟨(T₁ + 1 : ℝ) * Complex.I, by simp⟩
  have hconst : ∀ b, n b = n b₀ := fun b => by
    refine IsLocallyConstant.apply_eq_of_preconnectedSpace (f := n)
      ((IsLocallyConstant.iff_eventually_eq _).2 fun b' => ?_) b b₀
    obtain ⟨hi, hd, hs⟩ := zComb_lattice (lam b') (hbas b' (hT₁ b' b'.2).2).1 (hbas b' (hT₁ b' b'.2).2).2
    refine PerLim.eventually_eq_of_lattice (fun b : B => zComb (lam b)) hZc b' hi hd hs n ?_
    exact (hPc a₀).congr fun b => hn b
  obtain ⟨C, Bx, hC⟩ := hgrow R
  have hidx : ∀ (τ : E →+* ℂ) (m : ℕ), m = (if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q) →
      ∃ s : Fin m → Fin g, Function.Injective s ∧ ∀ i, relab c σ (e (s i)).1 = τ ∧ ((e (s i)).2 : ℕ) = i := by
    intro τ m hmτ
    obtain ⟨τ', rfl⟩ := Finite.injective_iff_surjective.1 (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_injective c σ) τ
    have h1 : m = Dw.mult τ' := by
      rw [hmτ, Datum.mult]
      exact if_congr (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_rt c σ hσ τ') rfl rfl
    subst h1
    refine ⟨fun i => e.symm ⟨τ', i⟩, fun i i' h => ?_, fun i => ?_⟩
    · exact eq_of_heq (Sigma.mk.inj (e.symm.injective h)).2
    · rw [Equiv.apply_symm_apply]
      exact ⟨rfl, rfl⟩
  have hlet : ∀ (τ : E →+* ℂ) (i : ℕ), (τ ∈ (U.X k).Ψ ∧ i < N - (U.X k).p0) ∨
      (conjEmb τ ∈ (U.X k).Ψ ∧ i < (U.X k).p0) → ∃ jj : Fin g, relab c σ (e jj).1 = τ ∧ ((e jj).2 : ℕ) = i := by
    intro τ i hτ
    rcases hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨s, -, hs⟩ := hidx τ (N - (U.X k).p0) (by
        rw [if_pos (((hX k).2 _).1 h1), (hX k).1, hN, Nat.add_sub_cancel])
      exact ⟨s ⟨i, h2⟩, hs _⟩
    · have hcc : NumberField.ComplexEmbedding.conjugate (conjEmb τ) = τ := RingHom.ext fun a => by
        simp [conjEmb, NumberField.ComplexEmbedding.conjugate_coe_eq]
      have hne : ¬ τ (H.rt : E) = H.rt0 := fun h =>
        ((U.X k).cmType (conjEmb τ)).1 h1 (by rw [hcc]; exact ((hX k).2 τ).2 h)
      obtain ⟨s, -, hs⟩ := hidx τ (U.X k).p0 (by rw [if_neg hne, (hX k).1])
      exact ⟨s ⟨i, h2⟩, hs _⟩
  refine ⟨(∑ j, (|n b₀ j| : ℝ)) * C, Bx, ?_⟩
  filter_upwards [(tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T₁)]
    with w hw hR τ i hτ
  obtain ⟨jj, hj1, hj2⟩ := hlet τ i hτ
  have hP : perFr (U.X k) (xx w) v τ i = Pm ⟨w, hw⟩ a₀ jj := by
    rw [hPm, hva, hj1, hj2]
  rw [hP, hn, hconst, zComb_apply]
  have hl := hC w (hT₁ w hw).2 hR
  calc ‖(∑ j, n b₀ j • lam (⟨w, hw⟩ : B) j) jj‖ ≤ ‖∑ j, n b₀ j • lam (⟨w, hw⟩ : B) j‖ := norm_le_pi_norm _ _
    _ ≤ ∑ j, ‖n b₀ j • lam w j‖ := norm_sum_le _ _
    _ ≤ ∑ j, (|n b₀ j| : ℝ) * ‖lam w‖ := Finset.sum_le_sum fun j _ => by
        rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, Real.norm_eq_abs, ← Int.cast_abs]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm _ _) (by positivity)
    _ = (∑ j, (|n b₀ j| : ℝ)) * ‖lam w‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ j, (|n b₀ j| : ℝ)) * (C * w.im ^ Bx) :=
        mul_le_mul_of_nonneg_left hl (Finset.sum_nonneg fun j _ => by positivity)
    _ = _ := (mul_assoc _ _ _).symm

end GlobalTheory.ShFam.PerPoly
