import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTie

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `h1 : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)}` using `Ideal.mem_span_singleton_self _`. Rewrite `h1` using `[← l.prod]`. Conclude with `(Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))) h1`.
-/
theorem mem_Mb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    (l.M : 𝓞 E) ∈ l.Mb := by
  have h1 : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
  rw [← l.prod] at h1
  exact (Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))) h1

/- English proof (translation)
Rewrite using `[Nat.cast_pow]`. Conclude with `Ideal.pow_mem_pow (mem_Mb l) 2`.
-/
theorem mem_Mb_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ((l.M ^ 2 : ℕ) : 𝓞 E) ∈ l.Mb ^ 2 := by
  rw [Nat.cast_pow]
  exact Ideal.pow_mem_pow (mem_Mb l) 2

/- English proof (translation)
Establish `act0 : t.act.act 0 = 1`. Establish `h0` using `t.act.add 0 0`. Rewrite `h0` using `[add_zero]`. Conclude with `mul_eq_left.1 h0.symm`. Proceed by induction on `n with`.

Consider the case `zero => rw [Nat.cast_zero, act0, pow_zero]`. Consider the case `succ n ih => rw [Nat.cast_succ, t.act.add, ih, t.act.one, pow_succ]`.
-/
theorem act_natCast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (n : ℕ) : t.act.act (n : 𝓞 E) = 𝟙 _ ^ n := by
  have act0 : t.act.act 0 = 1 := by
    have h0 := t.act.add 0 0
    rw [add_zero] at h0
    exact mul_eq_left.1 h0.symm
  induction n with
  | zero => rw [Nat.cast_zero, act0, pow_zero]
  | succ n ih => rw [Nat.cast_succ, t.act.add, ih, t.act.one, pow_succ]

/- English proof (translation)
Establish `e` using `h _ (mem_Mb_sq l)`. Rewrite `e` using `[act_natCast, MonObj.comp_pow, Category.comp_id]`. Conclude with `e`.
-/
theorem pow_of_killedBy {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (u : T ⟶ Xo.univ.t.G) (h : KilledBy Xo (l.Mb ^ 2) u) :
    u ^ (l.M ^ 2) = 1 := by
  have e := h _ (mem_Mb_sq l)
  rw [act_natCast, MonObj.comp_pow, Category.comp_id] at e
  exact e

/- English proof (translation)
Introduce `D T h j hj _ _ Tc io yI e la ho hy hM I hsplit x F hVt`. Set `_` to `io.toAlgebra`. Take `⟨P, hP⟩` from `hU D T h j hj Tc io yI e la ho hy hM I hsplit`. Take `⟨θ, hθ, θK, hθ1, hθ2⟩` from `hT _ _ _ _ _ _ Tc io yI.1 I`. Take `⟨ttK, FK, hVK, hFK⟩` from `hV _ _ _ _ _ yI.1.x I.t' I.m1 I.w1 I.rig1 T.Q.l.M _ yI.1.s _ F hVt (fun u hu => pow_of_killedBy _ u hu) θK hθ1`.

Take `⟨σ, hσ⟩` from `hR _ _ Tc.V I.G P hP θ hθ T.Q.l.M (isUnit_natCast_of_overLa Tc ho hM) I.t' I.m2 I.w2 I.rig2 θK hθ2 ttK FK hVK`. Take `⟨σt, hσt⟩` from `exists_restrict I.t' _ (zCast I.t'.G (natCast_sq T.Q.l.M) FK)`. Establish `hg : ∀ {Z : Scheme.{0}} (r : Z ⟶ I.t'.G.left), (r ≫ gsec I.t'.G) ≫ (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left = r` using `fun r => by`. Rewrite using `[Category.assoc, gsec_snd, Category.comp_id]`. Use `⟨σ, σt, fun Z r zp h1 h2 z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩` and prove the remaining obligations.

Rewrite using `[hσt Z r z J' hJ']`. Conclude with `hFK Z r zp (r ≫ gsec I.t'.G) h1 h2 (hg r) z J J' hJ hJ'`. Rewrite using `[hσt Z r z J' hJ']`. Conclude with `hσ Z r (r ≫ gsec I.t'.G) (hg r) z J J' hJ hJ'`.
-/
theorem regTie_of (hU : UnifAtIntLaSt) (hR : RegUnifSt) (hV : VtMoveSt) (hT : ThetaTieSt) : RegTieSt := by
  intro D T h j hj _ _ Tc io yI e la ho hy hM I hsplit x F hVt
  let _ := io.toAlgebra
  obtain ⟨P, hP⟩ := hU D T h j hj Tc io yI e la ho hy hM I hsplit
  obtain ⟨θ, hθ, θK, hθ1, hθ2⟩ := hT _ _ _ _ _ _ Tc io yI.1 I
  obtain ⟨ttK, FK, hVK, hFK⟩ := hV _ _ _ _ _ yI.1.x I.t' I.m1 I.w1 I.rig1 T.Q.l.M _ yI.1.s _ F hVt
    (fun u hu => pow_of_killedBy _ u hu) θK hθ1
  obtain ⟨σ, hσ⟩ := hR _ _ Tc.V I.G P hP θ hθ T.Q.l.M (isUnit_natCast_of_overLa Tc ho hM) I.t' I.m2 I.w2 I.rig2
    θK hθ2 ttK FK hVK
  obtain ⟨σt, hσt⟩ := exists_restrict I.t' _ (zCast I.t'.G (natCast_sq T.Q.l.M) FK)
  have hg : ∀ {Z : Scheme.{0}} (r : Z ⟶ I.t'.G.left),
      (r ≫ gsec I.t'.G) ≫ (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left = r := fun r => by
    rw [Category.assoc, gsec_snd, Category.comp_id]
  refine ⟨σ, σt, fun Z r zp h1 h2 z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · rw [hσt Z r z J' hJ']
    exact hFK Z r zp (r ≫ gsec I.t'.G) h1 h2 (hg r) z J J' hJ hJ'
  · rw [hσt Z r z J' hJ']
    exact hσ Z r (r ≫ gsec I.t'.G) (hg r) z J J' hJ hJ'

end ReciprocityTheory.ChartRestriction.G.PullbackSections
