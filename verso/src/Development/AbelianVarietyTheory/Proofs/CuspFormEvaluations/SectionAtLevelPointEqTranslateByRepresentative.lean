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
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FockLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppellHumbertFrameSemicharacter
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SectionReadingExistsUniqueIsTheta
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExpNsmulEqPowVt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalfIntegralGeneratorTraceEqOne

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal.VtLevel

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[tyAct, _root_.mul_assoc]`.
-/
theorem tyAct_natCast_mul {E : Type} [Field E] [NumberField E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (n : ℕ) (a : 𝓞 E)
    (z : Fin g → ℂ) : tyAct ty ((n : 𝓞 E) * a) z = (n : ℂ) • tyAct ty a z := by
  funext k
  simp [tyAct, _root_.mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[tyAct]`.
-/
theorem tyAct_natCast {E : Type} [Field E] [NumberField E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (n : ℕ)
    (z : Fin g → ℂ) : tyAct ty (n : 𝓞 E) z = (n : ℂ) • z := by
  funext k
  simp [tyAct]

/- English proof (translation)
Simplify using `[hermForm]`.
-/
theorem hermForm_smul_left' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (c • z) w = c * hermForm Hm z w := by
  simp [hermForm]

/- English proof (translation)
Simplify using `[hermForm, Matrix.mulVec_smul]`.
-/
theorem hermForm_two_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z ((2 : ℂ) • w) = 2 * hermForm Hm z w := by
  simp [hermForm, Matrix.mulVec_smul]

/- English proof (translation)
Simplify using `[hermForm]`.
-/
theorem hermForm_add_left' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm]

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using (Φ.e_ker 0).2 Φ.lat.zero_mem`. Consider the case `succ n ih => rw [Nat.cast_succ, add_smul, one_smul, Φ.e_add, ih, pow_succ]`.
-/
theorem e_natCast_smul (n : ℕ) (z : Fin g → ℂ) : Φ.e ((n : ℂ) • z) = Φ.e z ^ n := by
  induction n with
  | zero => simpa using (Φ.e_ker 0).2 Φ.lat.zero_mem
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, Φ.e_add, ih, pow_succ]

/- English proof (translation)
Rewrite using `[← Φ.e_ker]`. Establish `h1` using `Φ.e_add (z - w) w`. Rewrite `h1` using `[sub_add_cancel, h]`. Conclude with `(mul_eq_right.1 h1.symm)`.
-/
theorem sub_mem_of_e_eq {z w : Fin g → ℂ} (h : Φ.e z = Φ.e w) : z - w ∈ Φ.lat := by
  rw [← Φ.e_ker]
  have h1 := Φ.e_add (z - w) w
  rw [sub_add_cancel, h] at h1
  exact (mul_eq_right.1 h1.symm)

end

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1` using `H.bar_eq (H.bar a)`. Rewrite `h1` using `[H.bar_eq a, IsCMField.complexConj_apply_apply]`. Conclude with `h1`.
-/
theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  have h1 := H.bar_eq (H.bar a)
  rw [H.bar_eq a, IsCMField.complexConj_apply_apply] at h1
  exact h1

/- English proof (translation)
Establish `h1` using `Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hr`. Establish `h2 : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _` using `RingHom.ext fun a => bar_bar a`. Rewrite `h1` using `[Ideal.map_mul, Ideal.map_pow, Ideal.map_map, h2, Ideal.map_id, Ideal.map_span, Set.image_singleton, map_ofNat, Ideal.mem_span_singleton_mul]`. Take `⟨α, hα, h⟩` from `h1`. Conclude with `⟨α, hα, by rw [Nat.cast_ofNat, h]; rfl⟩`.
-/
theorem bar_mem {r : 𝓞 E} (hr : r ∈ Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) :
    ∃ α ∈ l.Mb ^ 2, H.bar r = ((2 : ℕ) : 𝓞 E) * α := by
  have h1 := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hr
  have h2 : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _ :=
    RingHom.ext fun a => bar_bar a
  rw [Ideal.map_mul, Ideal.map_pow, Ideal.map_map, h2, Ideal.map_id, Ideal.map_span, Set.image_singleton,
    map_ofNat, Ideal.mem_span_singleton_mul] at h1
  obtain ⟨α, hα, h⟩ := h1
  exact ⟨α, hα, by rw [Nat.cast_ofNat, h]; rfl⟩

/- English proof (translation)
Establish `h1` using `Submodule.smul_mem_smul hα hx`. Rewrite `h1` using `[← Submodule.mul_smul]`. Establish `h2 : l.Mb ^ 2 * (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) ≤ Ideal.span {((l.M ^ 2 : ℕ) : 𝓞 E)}`. Rewrite using `[mul_left_comm, ← mul_pow, l.prod, Ideal.span_singleton_pow, Nat.cast_pow]`. Conclude with `Ideal.mul_le_right`.

Establish `h3` using `Submodule.smul_mono_left h2 h1`. Rewrite `h3` using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨w, -, hw⟩` from `h3`. Conclude with `⟨w, hw.symm⟩`.
-/
theorem smul_eq_of_mem {x2 : Dw.La}
    (hx : x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La))
    {α : 𝓞 E} (hα : α ∈ l.Mb ^ 2) : ∃ w : Dw.La, α • x2 = ((l.M ^ 2 : ℕ) : 𝓞 E) • w := by
  have h1 := Submodule.smul_mem_smul hα hx
  rw [← Submodule.mul_smul] at h1
  have h2 : l.Mb ^ 2 * (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) ≤
      Ideal.span {((l.M ^ 2 : ℕ) : 𝓞 E)} := by
    rw [mul_left_comm, ← mul_pow, l.prod, Ideal.span_singleton_pow, Nat.cast_pow]
    exact Ideal.mul_le_right
  have h3 := Submodule.smul_mono_left h2 h1
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨w, -, hw⟩ := h3
  exact ⟨w, hw.symm⟩

/- English proof (translation)
Establish `h3` using `Submodule.smul_mono_left (Ideal.mul_le_left) hx`. Rewrite `h3` using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨w, -, hw⟩` from `h3`. Conclude with `⟨w, by rw [← hw, two_smul]⟩`.
-/
theorem eq_two_smul_of_mem {x2 : Dw.La}
    (hx : x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ w : Dw.La, x2 = w + w := by
  have h3 := Submodule.smul_mono_left (Ideal.mul_le_left) hx
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨w, -, hw⟩ := h3
  exact ⟨w, by rw [← hw, two_smul]⟩

variable {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

/- English proof (translation)
Use `forall₂_congr fun α _ => ?_` and prove the remaining obligations. Rewrite using `[← Φ.lin, Φ.e_ker]`.
-/
theorem killedBy_iff (I : Ideal (𝓞 E)) (z : Fin g → ℂ) :
    KilledBy Xo I (Φ.e z) ↔ ∀ α ∈ I, tyAct ty α z ∈ Φ.lat := by
  refine forall₂_congr fun α _ => ?_
  rw [← Φ.lin, Φ.e_ker]

/- English proof (translation)
Establish `h1` using `Xo.univ.eta_add (x2 - x) x`. Rewrite `h1` using `[sub_add_cancel, Xo.univ.eta_ker _ h, _root_.one_mul]`. Unfold `levPt`. Rewrite using `[h1]`.
-/
theorem levPt_eq {x x2 : Dw.La} (h : x2 - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    levPt Xo y.x x2 = levPt Xo y.x x := by
  have h1 := Xo.univ.eta_add (x2 - x) x
  rw [sub_add_cancel, Xo.univ.eta_ker _ h, _root_.one_mul] at h1
  unfold levPt
  rw [h1]

/- English proof (translation)
Use `Submodule.smul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `r hr w _`. Take `⟨α, hα, h⟩` from `bar_mem hr`. Take `⟨k, hk⟩` from `((anFr_semichar _ _ _ _ _ Φ.toAnFr).1 _ (hmk w) _ (hu α hα)).1`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Rewrite using `[hlin, Φ.adj, h, tyAct_natCast_mul, Nat.cast_ofNat, hermForm_two_right, ← hk]`. Simplify using the standard rewrite rules. Introduce and unpack `a b ⟨k, hk⟩ ⟨k', hk'⟩`. Use `⟨k + k', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hermForm_add_left', Complex.add_im, hk, hk']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem im_even (mk : Dw.La →+ (Fin g → ℂ)) (hmk : ∀ a, mk a ∈ Φ.lat)
    (hlin : ∀ (α : 𝓞 E) a, mk (α • a) = tyAct ty α (mk a)) {u : Fin g → ℂ}
    (hu : ∀ α ∈ l.Mb ^ 2, tyAct ty α u ∈ Φ.lat) {x2 : Dw.La}
    (hx : x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ k : ℤ, (hermForm Φ.Hm (mk x2) u).im = 2 * k := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr w _
    obtain ⟨α, hα, h⟩ := bar_mem hr
    obtain ⟨k, hk⟩ := ((anFr_semichar _ _ _ _ _ Φ.toAnFr).1 _ (hmk w) _ (hu α hα)).1
    refine ⟨k, ?_⟩
    rw [hlin, Φ.adj, h, tyAct_natCast_mul, Nat.cast_ofNat, hermForm_two_right, ← hk]
    simp
  · rintro a b ⟨k, hk⟩ ⟨k', hk'⟩
    refine ⟨k + k', ?_⟩
    rw [map_add, hermForm_add_left', Complex.add_im, hk, hk']
    push_cast
    ring

end

end GlobalTheory.AnVal.VtLevel

open GlobalTheory.AnVal.VtLevel in
/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ y g ty el Φ mk hmk hlin hlev θ hθ x x2 hx2 hx`. Establish `hM : (l.M : ℂ) ≠ 0`. Use `l.three_le` as an intermediate fact. Conclude with `Nat.cast_ne_zero.2 (by omega)`. Establish `hk : ∀ α ∈ l.Mb ^ 2, tyAct ty α (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ∈ Φ.lat`.

Introduce `α hα`. Take `⟨w, hw⟩` from `smul_eq_of_mem hx2 hα`. Rewrite using `[map_smul, ← hlin, hw, hlin, tyAct_natCast, smul_smul, Nat.cast_pow, inv_mul_cancel₀ (pow_ne_zero 2 hM), one_smul]`. Conclude with `hmk w`. Establish `hp : Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ^ l.M = levPt Xo y.x x`.

Establish `hm : x2 ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)` using `Submodule.smul_mono_left (Ideal.mul_le_right.trans (Ideal.pow_le_self two_ne_zero)) hx2`. Rewrite using `[← levPt_eq hx, hlev x2 hm, ← e_natCast_smul, smul_smul]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts. Use `⟨⟨(killedBy_iff Φ _ _).2 hk, hp⟩, fun F hF => ?_⟩` and prove the remaining obligations.

Establish `hχ : ∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1` using `fun a ha => (chi_eq_sign E H Dw l Xo c y g ty el Φ a ha).1`. Establish `hMm : ((l.M ^ 2 : ℕ) : 𝓞 E) ∈ l.Mb ^ 2`. Rewrite using `[Nat.cast_pow]`. Use `Ideal.pow_mem_pow ?_ 2` and prove the remaining obligations. Use `(Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) ?_` and prove the remaining obligations.

Rewrite using `[l.prod]`. Conclude with `Ideal.mem_span_singleton_self _`. Take `⟨x', δ, hδ, h2, hok, hpow, hrd⟩` from `(rd_vt_and_uu _ _ _ _ _ Φ.toAnFr hχ l.M l.odd y.s θ hθ).1 _ _ F hF (by`. Introduce `t' ht' _`. Take `⟨z, rfl⟩` from `Φ.e_onto t'`.

Establish `h1` using `(killedBy_iff Φ _ _).1 ht' _ hMm`. Rewrite `h1` using `[tyAct_natCast]`. Rewrite using `[← e_natCast_smul, Φ.e_ker]`. Conclude with `h1)`. Use `set a : Fin g → ℂ := ((l.M : ℂ) ^ 2)⁻¹ • mk x2 with ha`.

Establish `hu : ∀ α ∈ l.Mb ^ 2, tyAct ty α (x' - a) ∈ Φ.lat` using `fun α hα => by`. Rewrite using `[map_sub]`. Conclude with `Φ.lat.sub_mem ((killedBy_iff Φ _ _).1 hok α hα) (hk α hα)`. Establish `hb : (l.M : ℂ) • (x' - a) ∈ Φ.lat`. Rewrite using `[smul_sub]`.

Apply `sub_mem_of_e_eq` to reduce the goal to its premises. Rewrite using `[e_natCast_smul, e_natCast_smul, hpow, hp]`. Take `⟨w, hw⟩` from `eq_two_smul_of_mem hx2`. Take `⟨k, hk2⟩` from `l.odd`. Establish `hMa : ((l.M : ℂ) ^ 2) • a = mk w + mk w`.

Rewrite using `[ha, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hM), one_smul, hw, map_add]`. Establish `hb2 : (l.M : ℂ) • (x' - a) = (2 : ℂ) • (δ - mk w - k • ((l.M : ℂ) • (x' - a)))`. Establish `h3 : (l.M : ℂ) • ((l.M : ℂ) • (x' - a)) = (2 : ℂ) • δ - (mk w + mk w)`. Rewrite using `[smul_smul, ← sq, smul_sub, h2, hMa]`. Generalize the expression as in `(l.M : ℂ) • (x' - a) = b at h3 ⊢`.

Rewrite `h3` using `[hk2]`. Use function extensionality and compare the values at `i`. Use `congrFun h3 i` as an intermediate fact. Simplify using `only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at this ⊢`. Rewrite using `[nsmul_eq_mul]`.

Move the coercions through the operations in `at this`. Take the linear combination `this`. Establish `hχb : Φ.χ ((l.M : ℂ) • (x' - a)) = 1`. Rewrite using `[hb2]`. Conclude with `(anFr_semichar _ _ _ _ _ Φ.toAnFr).2.2 hχ _ (Φ.lat.sub_mem (Φ.lat.sub_mem hδ (hmk w)) (Φ.lat.nsmul_mem hb k))`.

Take `⟨f1, f2, f3⟩` from `fock_laws _ _ _ _ _ Φ.toAnFr`. Establish `hth` using `(reading_existsUnique_isTh _ _ _ _ _ Φ.toAnFr 1 y.s).2.1 θ hθ`. Take `⟨m, hm⟩` from `im_even Φ mk hmk hlin hu hx2`. Establish `hx' : x' = a + (x' - a)` using `by abel`. Rewrite `hrd` using `[hx', f1, f2 l.M (x' - a), f3 θ hth _ hb, hχb]`.

Establish `he : Complex.exp (((((l.M : ℤ) ^ 2 : ℤ) : ℂ)) * Real.pi * Complex.I * ((hermForm Φ.Hm a (x' - a)).im : ℂ)) = 1`. Establish `h4 : (hermForm Φ.Hm a (x' - a)).im = ((l.M : ℝ) ^ 2)⁻¹ * (2 * m)`. Rewrite using `[← hm]`. Use `nth_rewrite 1 [ha]`. Rewrite using `[hermForm_smul_left', ← Complex.im_ofReal_mul]`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[h4, ← Complex.exp_int_mul_two_pi_mul_I m]`. Use `congr 1`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite `hrd` using `[he]`. Simplify `hrd` using `only [_root_.one_mul]`.
-/
theorem GlobalTheory.AnVal.rd_vt_levPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ mk : Dw.La →+ (Fin g → ℂ), (∀ a, mk a ∈ Φ.lat) → (∀ (α : 𝓞 E) a, mk (α • a) = tyAct ty α (mk a)) → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • mk a)) → ∀ θ, Φ.toAnFr.Rd 1 y.s θ → ∀ x x2 : Dw.La, x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La) → x2 - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) → (KilledBy Xo (l.Mb ^ 2) (Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2)) ∧ Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ^ l.M = levPt Xo y.x x) ∧ ∀ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)), IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.s (levPt Xo y.x x) F → Φ.toAnFr.Rd ((l.M : ℤ) ^ 2) F (fock Φ.Hm ((l.M : ℤ) ^ 2) (((l.M : ℂ) ^ 2)⁻¹ • mk x2) fun z => θ ((l.M : ℂ) • z)) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ mk hmk hlin hlev θ hθ x x2 hx2 hx
  have hM : (l.M : ℂ) ≠ 0 := by
    have := l.three_le
    exact Nat.cast_ne_zero.2 (by omega)
  have hk : ∀ α ∈ l.Mb ^ 2, tyAct ty α (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ∈ Φ.lat := by
    intro α hα
    obtain ⟨w, hw⟩ := smul_eq_of_mem hx2 hα
    rw [map_smul, ← hlin, hw, hlin, tyAct_natCast, smul_smul, Nat.cast_pow, inv_mul_cancel₀ (pow_ne_zero 2 hM),
      one_smul]
    exact hmk w
  have hp : Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ^ l.M = levPt Xo y.x x := by
    have hm : x2 ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) :=
      Submodule.smul_mono_left (Ideal.mul_le_right.trans (Ideal.pow_le_self two_ne_zero)) hx2
    rw [← levPt_eq hx, hlev x2 hm, ← e_natCast_smul, smul_smul]
    congr 2
    field_simp
  refine ⟨⟨(killedBy_iff Φ _ _).2 hk, hp⟩, fun F hF => ?_⟩
  have hχ : ∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1 := fun a ha => (chi_eq_sign E H Dw l Xo c y g ty el Φ a ha).1
  have hMm : ((l.M ^ 2 : ℕ) : 𝓞 E) ∈ l.Mb ^ 2 := by
    rw [Nat.cast_pow]
    refine Ideal.pow_mem_pow ?_ 2
    refine (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) ?_
    rw [l.prod]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨x', δ, hδ, h2, hok, hpow, hrd⟩ :=
    (rd_vt_and_uu _ _ _ _ _ Φ.toAnFr hχ l.M l.odd y.s θ hθ).1 _ _ F hF (by
      intro t' ht' _
      obtain ⟨z, rfl⟩ := Φ.e_onto t'
      have h1 := (killedBy_iff Φ _ _).1 ht' _ hMm
      rw [tyAct_natCast] at h1
      rw [← e_natCast_smul, Φ.e_ker]
      exact h1)
  set a : Fin g → ℂ := ((l.M : ℂ) ^ 2)⁻¹ • mk x2 with ha
  have hu : ∀ α ∈ l.Mb ^ 2, tyAct ty α (x' - a) ∈ Φ.lat := fun α hα => by
    rw [map_sub]
    exact Φ.lat.sub_mem ((killedBy_iff Φ _ _).1 hok α hα) (hk α hα)
  have hb : (l.M : ℂ) • (x' - a) ∈ Φ.lat := by
    rw [smul_sub]
    apply sub_mem_of_e_eq
    rw [e_natCast_smul, e_natCast_smul, hpow, hp]
  obtain ⟨w, hw⟩ := eq_two_smul_of_mem hx2
  obtain ⟨k, hk2⟩ := l.odd
  have hMa : ((l.M : ℂ) ^ 2) • a = mk w + mk w := by
    rw [ha, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hM), one_smul, hw, map_add]
  have hb2 : (l.M : ℂ) • (x' - a) = (2 : ℂ) • (δ - mk w - k • ((l.M : ℂ) • (x' - a))) := by
    have h3 : (l.M : ℂ) • ((l.M : ℂ) • (x' - a)) = (2 : ℂ) • δ - (mk w + mk w) := by
      rw [smul_smul, ← sq, smul_sub, h2, hMa]
    generalize (l.M : ℂ) • (x' - a) = b at h3 ⊢
    rw [hk2] at h3
    funext i
    have := congrFun h3 i
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at this ⊢
    rw [nsmul_eq_mul]
    push_cast at this
    linear_combination this
  have hχb : Φ.χ ((l.M : ℂ) • (x' - a)) = 1 := by
    rw [hb2]
    exact (anFr_semichar _ _ _ _ _ Φ.toAnFr).2.2 hχ _
      (Φ.lat.sub_mem (Φ.lat.sub_mem hδ (hmk w)) (Φ.lat.nsmul_mem hb k))
  obtain ⟨f1, f2, f3⟩ := fock_laws _ _ _ _ _ Φ.toAnFr
  have hth := (reading_existsUnique_isTh _ _ _ _ _ Φ.toAnFr 1 y.s).2.1 θ hθ
  obtain ⟨m, hm⟩ := im_even Φ mk hmk hlin hu hx2
  have hx' : x' = a + (x' - a) := by abel
  rw [hx', f1, f2 l.M (x' - a), f3 θ hth _ hb, hχb] at hrd
  have he : Complex.exp (((((l.M : ℤ) ^ 2 : ℤ) : ℂ)) * Real.pi * Complex.I *
      ((hermForm Φ.Hm a (x' - a)).im : ℂ)) = 1 := by
    have h4 : (hermForm Φ.Hm a (x' - a)).im = ((l.M : ℝ) ^ 2)⁻¹ * (2 * m) := by
      rw [← hm]
      nth_rewrite 1 [ha]
      rw [hermForm_smul_left', ← Complex.im_ofReal_mul]
      push_cast
      rfl
    rw [h4, ← Complex.exp_int_mul_two_pi_mul_I m]
    congr 1
    push_cast
    field_simp
  rw [he] at hrd
  simpa only [_root_.one_mul] using hrd
