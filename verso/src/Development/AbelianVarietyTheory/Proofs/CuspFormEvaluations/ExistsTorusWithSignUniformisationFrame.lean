import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.TorusAtExists

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusSign

/- English proof (translation)
Establish `hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2` using `by rw [← map_pow, H.rt_sq]; simp`. Establish `hne : H.bar H.rt ≠ H.rt`. Introduce `h`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `h1 : IsCMField.complexConj E (H.rt : E) = H.rt` using `by rw [← H.bar_eq, h]`.

Establish `h2` using `IsCMField.complexEmbedding_complexConj E φ (H.rt : E)`. Rewrite `h2` using `[h1]`. Establish `h3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ)`. Use `congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq` as an intermediate fact. Simplify using `using this`.

Establish `him : (φ (H.rt : E)).im = 0` using `Complex.conj_eq_iff_im.1 h2.symm`. Establish `h4` using `congrArg Complex.re h3`. Simplify using `[sq, him] at h4`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Use polynomial arithmetic with `[mul_self_nonneg (φ (H.rt : E)).re]`.

Establish `hb : H.bar H.rt = -H.rt` using `(sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left hne`. Establish `h2 : 2 * H.bar H.w0 = 1 - H.rt`. Use `congrArg H.bar H.two_weight_eq_one_add_root` as an intermediate fact. Rewrite `this` using `[map_mul, map_add, map_one, hb, map_ofNat]`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `: (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1` using `by rw [mul_add, H.two_weight_eq_one_add_root, h2]; ring`. Conclude with `mul_left_cancel₀ two_ne_zero this`.
-/
theorem cmHostUnit_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  have hne : H.bar H.rt ≠ H.rt := by
    intro h
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 : IsCMField.complexConj E (H.rt : E) = H.rt := by rw [← H.bar_eq, h]
    have h2 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [h1] at h2
    have h3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
      simpa using this
    have him : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h2.symm
    have h4 := congrArg Complex.re h3
    simp [sq, him] at h4
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
  have hb : H.bar H.rt = -H.rt := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left hne
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, hb, map_ofNat] at this
    rw [this]; ring
  have : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by rw [mul_add, H.two_weight_eq_one_add_root, h2]; ring
  exact mul_left_cancel₀ two_ne_zero this

/- English proof (translation)
Establish `key : ∀ a b, Algebra.trace ℚ E (X.ξ0 * FD.herm X.Gm (φ a : Fin r → E) (φ b)) = -((D.EF a b : ℤ) : ℚ)`. Introduce `a b`. Rewrite using `[isom, neg_mul, map_neg, neg_neg]`. Use `GlobalTheory.torusAtExists E r X ?_ H.w0 ?_ x hx` and prove the remaining obligations. Introduce `f`.

Take `⟨a, ha⟩` from `D.unimod.2 (-(f.comp φ.toLinearMap.toAddMonoidHom).toIntLinearMap)`. Use `⟨φ a, (φ a).2, fun v => ?_⟩` and prove the remaining obligations. Take `⟨b, rfl⟩` from `φ.surjective v`. Rewrite using `[key, ha]`. Simplify using the standard rewrite rules.

Introduce `u hu v hv`. Take `⟨a, ha⟩` from `φ.surjective ⟨u, hu⟩`. Take `⟨b, hb⟩` from `φ.surjective ⟨v, hv⟩`. Establish `hu' : u = (φ a : Fin r → E)` using `by rw [ha]`. Establish `hv' : v = (φ b : Fin r → E)` using `by rw [hb]`.

Establish `hw : H.w0 - H.bar H.w0 = 1 - (H.bar H.w0 + H.bar H.w0)`. Use `cmHostUnit_add_conj_eq_one H` as an intermediate fact. Take the linear combination `this`. Establish `hs : ((H.w0 : E) - FD.cc (H.w0 : E)) • v = (φ ((H.w0 - H.bar H.w0) • b) : Fin r → E)`. Rewrite using `[map_smul, hb, FD.cc, ← H.bar_eq]`.

Use function extensionality and compare the values at `i`. Simplify using `[Algebra.smul_def]`. Use `⟨D.EF a (H.bar H.w0 • b), ?_⟩` and prove the remaining obligations. Rewrite using `[hs, hu', hv', key, key, hw, sub_smul, add_smul, one_smul, map_sub, map_add]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_torusAt_of_isom {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {r : ℕ} (X : FD.Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ)
    (isom : ∀ a b, ((D.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ E (-X.ξ0 * FD.herm X.Gm (φ a : Fin r → E) (φ b)))
    (x : FD.Frame X.Ψ r) (hx : x ∈ X.dom) : ∃ A : I2.TorusAt X x, A.w0 = H.w0 := by
  have key : ∀ a b, Algebra.trace ℚ E (X.ξ0 * FD.herm X.Gm (φ a : Fin r → E) (φ b)) = -((D.EF a b : ℤ) : ℚ) := by
    intro a b
    rw [isom, neg_mul, map_neg, neg_neg]
  refine GlobalTheory.torusAtExists E r X ?_ H.w0 ?_ x hx
  · intro f
    obtain ⟨a, ha⟩ := D.unimod.2 (-(f.comp φ.toLinearMap.toAddMonoidHom).toIntLinearMap)
    refine ⟨φ a, (φ a).2, fun v => ?_⟩
    obtain ⟨b, rfl⟩ := φ.surjective v
    rw [key, ha]
    simp
  · intro u hu v hv
    obtain ⟨a, ha⟩ := φ.surjective ⟨u, hu⟩
    obtain ⟨b, hb⟩ := φ.surjective ⟨v, hv⟩
    have hu' : u = (φ a : Fin r → E) := by rw [ha]
    have hv' : v = (φ b : Fin r → E) := by rw [hb]
    have hw : H.w0 - H.bar H.w0 = 1 - (H.bar H.w0 + H.bar H.w0) := by
      have := cmHostUnit_add_conj_eq_one H
      linear_combination this
    have hs : ((H.w0 : E) - FD.cc (H.w0 : E)) • v = (φ ((H.w0 - H.bar H.w0) • b) : Fin r → E) := by
      rw [map_smul, hb, FD.cc, ← H.bar_eq]
      funext i
      simp [Algebra.smul_def]
    refine ⟨D.EF a (H.bar H.w0 • b), ?_⟩
    rw [hs, hu', hv', key, key, hw, sub_smul, add_smul, one_smul, map_sub, map_add]
    push_cast
    ring

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U k x W`. Conclude with `exists_torusAt_of_isom (W.F.Di (W.ik k)) (U.X k) (W.φ k) (W.isom k) x.1 x.2`.
-/
theorem exists_torusAt_w0_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x), ∃ A : I2.TorusAt (U.X k) x.1, A.w0 = H.w0 := by
  intro E _ _ _ H Dw l Xo c σ r U k x W
  exact exists_torusAt_of_isom (W.F.Di (W.ik k)) (U.X k) (W.φ k) (W.isom k) x.1 x.2

end GlobalTheory.TorusSign
