import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasisStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLatticesStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieMultIffFinrank

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.EigDec

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `h.1.hom_ext hxy` to reduce the goal to its premises. Rewrite using `[Over.w x, Over.w y]`.
-/
private theorem hom_ext_lemma {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {x y : G' ⟶ G'} (hxy : x.left ≫ φ = y.left ≫ φ) :
    x = y := by
  apply Over.OverMorphism.ext
  apply h.1.hom_ext hxy
  rw [Over.w x, Over.w y]

/- English proof (translation)
Set `Φ : Over.mk (G'.hom ≫ f) ⟶ G` to `Over.homMk φ h.1.w`. Use `⟨{ act := b, hom := hb, one := ?_, mul := ?_, add := ?_ }, rfl⟩` and prove the remaining obligations. Apply `hom_ext_lemma h` to reduce the goal to its premises. Rewrite using `[e 1, act.one]`. Simplify using the standard rewrite rules.

Introduce `a a'`. Apply `hom_ext_lemma h` to reduce the goal to its premises. Rewrite using `[e (a * a'), act.mul, Over.comp_left, Over.comp_left, Category.assoc, e a', ← Category.assoc (b a).left, e a, Category.assoc]`. Introduce `a a'`. Apply `hom_ext_lemma h` to reduce the goal to its premises.

Establish `hx : (Φ ≫ act.act a).left = (b a).left ≫ φ`. Rewrite using `[e a]`. Both sides reduce to the same expression. Establish `hy : (Φ ≫ act.act a').left = (b a').left ≫ φ`. Rewrite using `[e a']`.

Both sides reduce to the same expression. Establish `key` using `h.2 G' (b a) (b a') (Φ ≫ act.act a) (Φ ≫ act.act a') hx hy`. Rewrite using `[← key, ← MonObj.comp_mul, ← act.add, e (a + a')]`. Both sides reduce to the same expression.
-/
theorem exists_oAct {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {O : Type} [CommRing O] (act : OAct O G)
    (b : O → (G' ⟶ G')) (hb : ∀ a, IsMonHom (b a)) (e : ∀ a, (b a).left ≫ φ = φ ≫ (act.act a).left) :
    ∃ act' : OAct O G', act'.act = b := by
  let Φ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  refine ⟨{ act := b, hom := hb, one := ?_, mul := ?_, add := ?_ }, rfl⟩
  · apply hom_ext_lemma h
    rw [e 1, act.one]
    simp
  · intro a a'
    apply hom_ext_lemma h
    rw [e (a * a'), act.mul, Over.comp_left, Over.comp_left, Category.assoc, e a', ← Category.assoc (b a).left, e a,
      Category.assoc]
  · intro a a'
    apply hom_ext_lemma h
    have hx : (Φ ≫ act.act a).left = (b a).left ≫ φ := by
      rw [e a]
      rfl
    have hy : (Φ ≫ act.act a').left = (b a').left ≫ φ := by
      rw [e a']
      rfl
    have key := h.2 G' (b a) (b a') (Φ ≫ act.act a) (Φ ≫ act.act a') hx hy
    rw [← key, ← MonObj.comp_mul, ← act.add, e (a + a')]
    rfl

/- English proof (translation)
Establish `hA : ∀ c : Fin F.P₀.g → K, IsLieComb c F.v (ReciprocityTheory.ChartRestriction.G.Chart.prodPts c F.v)` using `fun c => ⟨fun i => Chart.spMap (Chart.scaleD (c i)) ≫ F.v i, fun i => rfl, rfl⟩`. Establish `hB : ∀ (c : Fin F.P₀.g → K) w, IsLieComb c F.v w → w = ReciprocityTheory.ChartRestriction.G.Chart.prodPts c F.v`. Introduce and unpack `c w ⟨u, hu, rfl⟩`. Use `show (List.ofFn u).prod = (List.ofFn fun i => Chart.spMap (Chart.scaleD (c i)) ≫ F.v i).prod`. Use `congr 1`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hu i]`. Both sides reduce to the same expression.

Establish `hl : ∀ a, ∃ f₀ : F.P₀.A ⟶ F.P₀.A, IsMonHom f₀ ∧ f₀.left ≫ F.φ = F.φ ≫ (act.act a).left ∧ ∀ M, F.IsDiffOf F (act.act a) M → ∀ c w, IsLieComb c F.v w → IsLieComb (M c) F.v (w ≫ f₀)` using `fun a => (GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P F (act.act a) (act.hom a)).2`. Use `choose b hb he hlie using hl`. Take `⟨act', hact'⟩` from `exists_oAct F.fib.2.1 act b hb he`. Establish `ha : ∀ a, (act'.act a).left ≫ F.φ = F.φ ≫ (act.act a).left`. Introduce `a`.

Rewrite using `[hact']`. Conclude with `he a`. Establish `hρ : ∀ a c, ReciprocityTheory.ChartRestriction.G.Chart.prodPts (r a c) F.v = ReciprocityTheory.ChartRestriction.G.Chart.prodPts c F.v ≫ act'.act a`. Introduce `a c`. Rewrite using `[hact']`.

Conclude with `(hB _ _ (hlie a (r a) (hr a) c _ (hA c))).symm`. Use `haveI : IsCommMonObj F.P₀.A := F.P₀.isAb.comm`. Use `haveI : Smooth F.P₀.A.hom := by haveI := F.P₀.smoothDim`. Conclude with `SmoothOfRelativeDimension.smooth F.P₀.g F.P₀.A.hom`. Establish `hN1 : LieMult act (spMap j ≫ spMap (algebraMap (𝓞 K) K)) (j.comp χ) N`.

Rewrite using `[← spMap_comp]`. Conclude with `hN`. Establish `hN2` using `(GlobalTheory.LiePull.lieMult_pull O (Sp (𝓞 K)) (Sp K) P.A F.P₀.A (spMap (algebraMap (𝓞 K) K)) F.φ act act' F.fib.2.1 ha k (spMap j) (j.comp χ) N).mpr hN1`. Establish `hN3` using `(GlobalTheory.LieExt.lieMult_extend_iff j F.P₀.A act' χ N).mp hN2`. Establish `hN4` using `(GlobalTheory.LiePull.lieMult_pull O (Sp (𝓞 K)) (Sp K) P.A F.P₀.A (spMap (algebraMap (𝓞 K) K)) F.φ act act' F.fib.2.1 ha K (𝟙 _) χ N).mp hN3`.

Rewrite `hN4` using `[Category.id_comp]`. Conclude with `GlobalTheory.LieEigen.finrank_of_lieMult F.fib.2.1 F.basis ha hρ hN4`.
-/
theorem finrank_eigenSub {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P)
    {O : Type} [CommRing O] (act : OAct O P.A) (r : O →+* Module.End K (Fin F.P₀.g → K))
    (hr : ∀ a, F.IsDiffOf F (act.act a) (r a)) {k : Type} [Field k] (j : K →+* k) (χ : O →+* K) {N : ℕ}
    (hN : LieMult act (spMap (j.comp (algebraMap (𝓞 K) K))) (j.comp χ) N) :
    Module.finrank K (EigenSplit.eigenSub r χ) = N := by
  classical
  have hA : ∀ c : Fin F.P₀.g → K, IsLieComb c F.v (ReciprocityTheory.ChartRestriction.G.Chart.prodPts c F.v) :=
    fun c => ⟨fun i => Chart.spMap (Chart.scaleD (c i)) ≫ F.v i, fun i => rfl, rfl⟩
  have hB : ∀ (c : Fin F.P₀.g → K) w, IsLieComb c F.v w → w = ReciprocityTheory.ChartRestriction.G.Chart.prodPts c F.v := by
    rintro c w ⟨u, hu, rfl⟩
    show (List.ofFn u).prod = (List.ofFn fun i => Chart.spMap (Chart.scaleD (c i)) ≫ F.v i).prod
    congr 1
    congr 1
    funext i
    apply Over.OverMorphism.ext
    rw [hu i]
    rfl
  have hl : ∀ a, ∃ f₀ : F.P₀.A ⟶ F.P₀.A, IsMonHom f₀ ∧ f₀.left ≫ F.φ = F.φ ≫ (act.act a).left ∧
      ∀ M, F.IsDiffOf F (act.act a) M → ∀ c w, IsLieComb c F.v w → IsLieComb (M c) F.v (w ≫ f₀) :=
    fun a => (GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P F (act.act a) (act.hom a)).2
  choose b hb he hlie using hl
  obtain ⟨act', hact'⟩ := exists_oAct F.fib.2.1 act b hb he
  have ha : ∀ a, (act'.act a).left ≫ F.φ = F.φ ≫ (act.act a).left := by
    intro a
    rw [hact']
    exact he a
  have hρ : ∀ a c, ReciprocityTheory.ChartRestriction.G.Chart.prodPts (r a c) F.v = ReciprocityTheory.ChartRestriction.G.Chart.prodPts c F.v ≫ act'.act a := by
    intro a c
    rw [hact']
    exact (hB _ _ (hlie a (r a) (hr a) c _ (hA c))).symm
  haveI : IsCommMonObj F.P₀.A := F.P₀.isAb.comm
  haveI : Smooth F.P₀.A.hom := by
    haveI := F.P₀.smoothDim
    exact SmoothOfRelativeDimension.smooth F.P₀.g F.P₀.A.hom
  have hN1 : LieMult act (spMap j ≫ spMap (algebraMap (𝓞 K) K)) (j.comp χ) N := by
    rw [← spMap_comp]
    exact hN
  have hN2 := (GlobalTheory.LiePull.lieMult_pull O (Sp (𝓞 K)) (Sp K) P.A F.P₀.A (spMap (algebraMap (𝓞 K) K)) F.φ act act'
    F.fib.2.1 ha k (spMap j) (j.comp χ) N).mpr hN1
  have hN3 := (GlobalTheory.LieExt.lieMult_extend_iff j F.P₀.A act' χ N).mp hN2
  have hN4 := (GlobalTheory.LiePull.lieMult_pull O (Sp (𝓞 K)) (Sp K) P.A F.P₀.A (spMap (algebraMap (𝓞 K) K)) F.φ act act'
    F.fib.2.1 ha K (𝟙 _) χ N).mp hN3
  rw [Category.id_comp] at hN4
  exact GlobalTheory.LieEigen.finrank_of_lieMult F.fib.2.1 F.basis ha hρ hN4

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

/- English proof (translation)
Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hz : φ (H.rt : E) ^ 2 = -(H.d : ℂ)`. Establish `h` using `congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq`. Simplify using `using h`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`.

Establish `hre` using `congrArg Complex.re hz`. Establish `him` using `congrArg Complex.im hz`. Simplify using `only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him`. Establish `h0 : (φ (H.rt : E)).re = 0`. Break down `mul_eq_zero.mp (show (φ (H.rt : E)).re * (φ (H.rt : E)).im = 0 by linarith) with h | h` into its components or cases.

Conclude with `h`. Rewrite `hre` using `[h]`. Use polynomial arithmetic with `[mul_self_nonneg (φ (H.rt : E)).re]`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Apply `φ.injective` to reduce the goal to its premises.

Rewrite using `[H.bar_eq, IsCMField.complexEmbedding_complexConj]`. Apply the tactic sequence `apply Complex.ext <;> simp [h0]`.
-/
theorem bar_rt : H.bar H.rt = -H.rt := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hz : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
    simpa using h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have h0 : (φ (H.rt : E)).re = 0 := by
    rcases mul_eq_zero.mp (show (φ (H.rt : E)).re * (φ (H.rt : E)).im = 0 by linarith) with h | h
    · exact h
    · rw [h] at hre
      nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
  apply RingOfIntegers.ext
  apply φ.injective
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
  apply Complex.ext <;> simp [h0]

/- English proof (translation)
Establish `hd0 : (H.d : 𝓞 K) ≠ 0` using `by exact_mod_cast H.d_prime.ne_zero`. Establish `hρ0 : ρ ≠ 0`. Introduce and unpack `rfl`. Apply `hd0` to reduce the goal to its premises. Simplify using `using hρ.symm`.

Establish `hne : ρ ≠ -ρ`. Introduce `h`. Apply `hρ0` to reduce the goal to its premises. Establish `h2 : (2 : 𝓞 K) * ρ = 0` using `by linear_combination h`. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases.

Conclude with `absurd h3 two_ne_zero`. Conclude with `h3`. Establish `key : ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ ∨ τ H.rt = -ρ`. Introduce `τ`. Apply `sq_eq_sq_iff_eq_or_eq_neg.mp` to reduce the goal to its premises.

Rewrite using `[← map_pow, H.rt_sq, hρ]`. Simplify using the standard rewrite rules. Establish `part1 : ∀ τ : 𝓞 E →+* 𝓞 K, ¬ τ H.rt = ρ ↔ τ H.rt = -ρ`. Introduce `τ`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `(key τ).resolve_left h`. Introduce `h h'`. Conclude with `hne (h'.symm.trans h)`. Establish `hbar : H.bar H.rt = -H.rt` using `bar_rt H`.

Set `e : {τ : 𝓞 E →+* 𝓞 K // τ H.rt = ρ} ≃ {τ : 𝓞 E →+* 𝓞 K // τ H.rt = -ρ}` to `{ toFun := fun τ => ⟨τ.1.comp H.bar.toRingHom, by simp [hbar, τ.2]⟩ invFun := fun τ => ⟨τ.1.comp H.bar.toRingHom, by simp [hbar, τ.2]⟩ left_inv := fun τ => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`. Simplify using the standard rewrite rules.

Use `right_inv := fun τ => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`. Simplify using `}`.

Establish `hpos : 0 < Module.finrank ℚ E` using `Module.finrank_pos`. Establish `hfin : Finite (𝓞 E →+* 𝓞 K)` using `Nat.finite_of_card_ne_zero (by rw [hs]; omega)`. Establish `hsum : Nat.card (𝓞 E →+* 𝓞 K) = Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = ρ} + Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = -ρ}`. Rewrite using `[← Nat.card_congr (Equiv.sumCompl fun τ : 𝓞 E →+* 𝓞 K => τ H.rt = ρ), Nat.card_sum]`. Use `congr 1`.

Conclude with `Nat.card_congr (Equiv.subtypeEquivRight part1)`. Establish `heq : Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = ρ} = Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = -ρ}` using `Nat.card_congr e`. Rewrite `hsum` using `[hs]`. Apply the tactic sequence `refine ⟨part1, ?_, ?_⟩ <;> omega`.
-/
theorem card_half {K : Type} [Field K] [NumberField K] {ρ : 𝓞 K} (hs : Splits E K) (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) :
    (∀ τ : 𝓞 E →+* 𝓞 K, ¬ τ H.rt = ρ ↔ τ H.rt = -ρ) ∧
    Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = ρ} = Module.finrank ℚ E / 2 ∧
    Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = -ρ} = Module.finrank ℚ E / 2 := by
  have hd0 : (H.d : 𝓞 K) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    apply hd0
    simpa using hρ.symm
  have hne : ρ ≠ -ρ := by
    intro h
    apply hρ0
    have h2 : (2 : 𝓞 K) * ρ = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 two_ne_zero
    · exact h3
  have key : ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ ∨ τ H.rt = -ρ := by
    intro τ
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [← map_pow, H.rt_sq, hρ]
    simp
  have part1 : ∀ τ : 𝓞 E →+* 𝓞 K, ¬ τ H.rt = ρ ↔ τ H.rt = -ρ := by
    intro τ
    constructor
    · intro h
      exact (key τ).resolve_left h
    · intro h h'
      exact hne (h'.symm.trans h)
  have hbar : H.bar H.rt = -H.rt := bar_rt H
  let e : {τ : 𝓞 E →+* 𝓞 K // τ H.rt = ρ} ≃ {τ : 𝓞 E →+* 𝓞 K // τ H.rt = -ρ} :=
    { toFun := fun τ => ⟨τ.1.comp H.bar.toRingHom, by simp [hbar, τ.2]⟩
      invFun := fun τ => ⟨τ.1.comp H.bar.toRingHom, by simp [hbar, τ.2]⟩
      left_inv := fun τ => by
        apply Subtype.ext
        apply RingHom.ext
        intro a
        simp
      right_inv := fun τ => by
        apply Subtype.ext
        apply RingHom.ext
        intro a
        simp }
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hfin : Finite (𝓞 E →+* 𝓞 K) := Nat.finite_of_card_ne_zero (by rw [hs]; omega)
  classical
  have hsum : Nat.card (𝓞 E →+* 𝓞 K) =
      Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = ρ} + Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = -ρ} := by
    rw [← Nat.card_congr (Equiv.sumCompl fun τ : 𝓞 E →+* 𝓞 K => τ H.rt = ρ), Nat.card_sum]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight part1)
  have heq : Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = ρ} = Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = -ρ} :=
    Nat.card_congr e
  rw [hs] at hsum
  refine ⟨part1, ?_, ?_⟩ <;> omega

/- English proof (translation)
Establish `hcard : Fintype.card (𝓞 E₁ →+* 𝓞 K₁) = Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E₁))`. Rewrite using `[← Nat.card_eq_fintype_card, hs, ← RingOfIntegers.rank E₁, Module.finrank_eq_card_chooseBasisIndex]`. Set `b` to `(RingOfIntegers.basis E₁).reindex (Fintype.equivOfCardEq hcard).symm`. Rewrite using `[EigenSplit.isSplitting_iff_isUnit_det _ b, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]`. Establish `hinj : Function.Injective fun τ : 𝓞 E₁ →+* 𝓞 K₁ => ((algebraMap (𝓞 K₁) K₁).comp τ).toMonoidHom`.

Introduce `τ τ' hττ`. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`. Establish `h1` using `congrArg (fun f : 𝓞 E₁ →* K₁ => f a) hττ`. Conclude with `FaithfulSMul.algebraMap_injective (𝓞 K₁) K₁ h1`.

Establish `hind` using `(linearIndependent_monoidHom (𝓞 E₁) K₁).comp _ hinj`. Rewrite `hind`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Apply `hind g` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Establish `hrow : ∀ i, ∑ τ, g τ * ((algebraMap (𝓞 K₁) K₁).comp τ) (b i) = 0`. Introduce `i`. Use `congrFun hg i` as an intermediate fact. Simplify using `using this`. Establish `hx : ∀ τ : 𝓞 E₁ →+* 𝓞 K₁, ((algebraMap (𝓞 K₁) K₁).comp τ) x = ∑ i, ((b.repr x i : ℤ) : K₁) * ((algebraMap (𝓞 K₁) K₁).comp τ) (b i)`.

Introduce `τ`. Use `conv_lhs => rw [← b.sum_repr x]`. Rewrite using `[map_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Rewrite using `[map_zsmul, zsmul_eq_mul]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply, MonoidHom.coe_coe]`. Use `show ∑ τ : 𝓞 E₁ →+* 𝓞 K₁, g τ * ((algebraMap (𝓞 K₁) K₁).comp τ) x = 0`. Simplify using `only [hx, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Establish `h2` using `hrow i`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `τ _`. Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by rw [h2, mul_zero]`.
-/
private theorem isSplitting_of_splits {E₁ K₁ : Type} [Field E₁] [NumberField E₁] [Field K₁] [NumberField K₁]
    [Fintype (𝓞 E₁ →+* 𝓞 K₁)] (hs : Splits E₁ K₁) :
    EigenSplit.IsSplitting fun τ : 𝓞 E₁ →+* 𝓞 K₁ => (algebraMap (𝓞 K₁) K₁).comp τ := by
  classical
  have hcard : Fintype.card (𝓞 E₁ →+* 𝓞 K₁) = Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E₁)) := by
    rw [← Nat.card_eq_fintype_card, hs, ← RingOfIntegers.rank E₁, Module.finrank_eq_card_chooseBasisIndex]
  let b := (RingOfIntegers.basis E₁).reindex (Fintype.equivOfCardEq hcard).symm
  rw [EigenSplit.isSplitting_iff_isUnit_det _ b, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_rows_iff_isUnit]
  have hinj : Function.Injective fun τ : 𝓞 E₁ →+* 𝓞 K₁ => ((algebraMap (𝓞 K₁) K₁).comp τ).toMonoidHom := by
    intro τ τ' hττ
    apply RingHom.ext
    intro a
    have h1 := congrArg (fun f : 𝓞 E₁ →* K₁ => f a) hττ
    exact FaithfulSMul.algebraMap_injective (𝓞 K₁) K₁ h1
  have hind := (linearIndependent_monoidHom (𝓞 E₁) K₁).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hind ⊢
  intro g hg
  apply hind g
  funext x
  have hrow : ∀ i, ∑ τ, g τ * ((algebraMap (𝓞 K₁) K₁).comp τ) (b i) = 0 := by
    intro i
    have := congrFun hg i
    simpa using this
  have hx : ∀ τ : 𝓞 E₁ →+* 𝓞 K₁, ((algebraMap (𝓞 K₁) K₁).comp τ) x =
      ∑ i, ((b.repr x i : ℤ) : K₁) * ((algebraMap (𝓞 K₁) K₁).comp τ) (b i) := by
    intro τ
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul, zsmul_eq_mul]
  simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply,
    MonoidHom.coe_coe]
  show ∑ τ : 𝓞 E₁ →+* 𝓞 K₁, g τ * ((algebraMap (𝓞 K₁) K₁).comp τ) x = 0
  simp only [hx, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  have h2 := hrow i
  calc ∑ τ : 𝓞 E₁ →+* 𝓞 K₁, g τ * (((b.repr x i : ℤ) : K₁) * ((algebraMap (𝓞 K₁) K₁).comp τ) (b i))
      = ((b.repr x i : ℤ) : K₁) * ∑ τ, g τ * ((algebraMap (𝓞 K₁) K₁).comp τ) (b i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro τ _
        ring
    _ = 0 := by rw [h2, mul_zero]

/- English proof (translation)
Introduce `E _ _ _ H K _ _ ρ T F p q hs hT hρ`. Take `⟨r, hr, hrl⟩` from `GlobalTheory.T.exists_lieRepresentation_eigenLattices K T.pol F (𝓞 E) T.t.act`. Establish `hfin : Finite (𝓞 E →+* 𝓞 K)` using `Nat.finite_of_card_ne_zero (by rw [hs]; exact (Module.finrank_pos (R := ℚ) (M := E)).ne')`. Use `haveI := Fintype.ofFinite (𝓞 E →+* 𝓞 K)`. Establish `hspan : ∀ τ : 𝓞 E →+* 𝓞 K, Submodule.span K (F.eigLat T.t.act τ : Set (Fin F.P₀.g → K)) = EigenSplit.eigenSub r ((algebraMap (𝓞 K) K).comp τ)`.

Introduce `τ`. Use extensionality with `c`. Rewrite using `[(hrl τ c).2, EigenSplit.mem_eigenSub]`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, algebraMap_smul]`. Establish `hsplit` using `isSplitting_of_splits (E₁ := E) (K₁ := K) hs`.

Establish `hint` using `EigenSplit.isInternal_eigenSub hsplit r`. Establish `hrank : ∀ τ : 𝓞 E →+* 𝓞 K, Module.finrank K (EigenSplit.eigenSub r ((algebraMap (𝓞 K) K).comp τ)) = if τ H.rt = ρ then p else q`. Introduce `τ`. Establish `hβ : Function.Injective ((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K))` using `(algebraMap K (AlgebraicClosure K)).injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)`. Take `⟨h1, h2⟩` from `hT (AlgebraicClosure K) ((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K)) hβ (((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K)).comp τ)`.

Establish `hiff : (((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K)).comp τ) H.rt = ((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K)) ρ ↔ τ H.rt = ρ` using `hβ.eq_iff`. Use `split_ifs with hτ`. Conclude with `finrank_eigenSub F T.t.act r hr (algebraMap K (AlgebraicClosure K)) ((algebraMap (𝓞 K) K).comp τ) (h1 (hiff.mpr hτ))`. Conclude with `finrank_eigenSub F T.t.act r hr (algebraMap K (AlgebraicClosure K)) ((algebraMap (𝓞 K) K).comp τ) (h2 (fun h => hτ (hiff.mp h)))`. Establish `hfun : (fun τ : 𝓞 E →+* 𝓞 K => Submodule.span K (F.eigLat T.t.act τ : Set (Fin F.P₀.g → K))) = fun τ => EigenSplit.eigenSub r ((algebraMap (𝓞 K) K).comp τ)` using `funext hspan`.

Take `⟨hpart, hc1, hc2⟩` from `card_half H hs hρ`. Establish `hsum : ∑ τ : 𝓞 E →+* 𝓞 K, (if τ H.rt = ρ then p else q) = Module.finrank ℚ E / 2 * (p + q)`. Rewrite using `[Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]`. Establish `e1 : (Finset.univ.filter fun τ : 𝓞 E →+* 𝓞 K => τ H.rt = ρ).card = Module.finrank ℚ E / 2`. Rewrite using `[← hc1, Nat.card_eq_fintype_card, Fintype.card_subtype]`.

Establish `e2 : (Finset.univ.filter fun τ : 𝓞 E →+* 𝓞 K => ¬ τ H.rt = ρ).card = Module.finrank ℚ E / 2`. Rewrite using `[← hc2, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Use `congr 1`. Use extensionality with `τ`. Simplify using `[hpart τ]`.

Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdim : Module.finrank K (Fin F.P₀.g → K) = ∑ τ : 𝓞 E →+* 𝓞 K, Module.finrank K (EigenSplit.eigenSub r ((algebraMap (𝓞 K) K).comp τ))`. Rewrite using `[(EigenSplit.eigenEquiv hsplit r).finrank_eq, Module.finrank_pi_fintype]`. Establish `hg : F.P₀.g = T.g` using `F.fib.1`.

Use `⟨?_, ?_, ?_, ?_, hc1, hc2⟩` and prove the remaining obligations. Introduce `τ`. Unfold `latRank`. Rewrite using `[hspan, hrank]`. Rewrite using `[hfun]`.

Conclude with `hint.submodule_iSupIndep`. Rewrite using `[hfun]`. Conclude with `hint.submodule_iSup_eq_top`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hdim]`.

Conclude with `Finset.sum_congr rfl fun τ _ => hrank τ`. Use `_ = Module.finrank ℚ E / 2 * (p + q) := hsum`.
-/
theorem eigen_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (T : PAT H (Sp (𝓞 K))) (F : GenFib T.pol) (p q : ℕ), Splits E K → HasType H T.t.act ρ p q → ρ ^ 2 = -(H.d : 𝓞 K) → (∀ τ : 𝓞 E →+* 𝓞 K, latRank K (F.eigLat T.t.act τ) = open Classical in if τ H.rt = ρ then p else q) ∧ iSupIndep (fun τ : 𝓞 E →+* 𝓞 K => Submodule.span K (F.eigLat T.t.act τ : Set (Fin F.P₀.g → K))) ∧ ⨆ τ : 𝓞 E →+* 𝓞 K, Submodule.span K (F.eigLat T.t.act τ : Set (Fin F.P₀.g → K)) = ⊤ ∧ T.g = Module.finrank ℚ E / 2 * (p + q) ∧ Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = ρ} = Module.finrank ℚ E / 2 ∧ Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = -ρ} = Module.finrank ℚ E / 2 := by
  intro E _ _ _ H K _ _ ρ T F p q hs hT hρ
  classical
  obtain ⟨r, hr, hrl⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K T.pol F (𝓞 E) T.t.act
  have hfin : Finite (𝓞 E →+* 𝓞 K) :=
    Nat.finite_of_card_ne_zero (by rw [hs]; exact (Module.finrank_pos (R := ℚ) (M := E)).ne')
  haveI := Fintype.ofFinite (𝓞 E →+* 𝓞 K)
  have hspan : ∀ τ : 𝓞 E →+* 𝓞 K, Submodule.span K (F.eigLat T.t.act τ : Set (Fin F.P₀.g → K)) =
      EigenSplit.eigenSub r ((algebraMap (𝓞 K) K).comp τ) := by
    intro τ
    ext c
    rw [(hrl τ c).2, EigenSplit.mem_eigenSub]
    simp only [RingHom.coe_comp, Function.comp_apply, algebraMap_smul]
  have hsplit := isSplitting_of_splits (E₁ := E) (K₁ := K) hs
  have hint := EigenSplit.isInternal_eigenSub hsplit r
  have hrank : ∀ τ : 𝓞 E →+* 𝓞 K, Module.finrank K (EigenSplit.eigenSub r ((algebraMap (𝓞 K) K).comp τ)) =
      if τ H.rt = ρ then p else q := by
    intro τ
    have hβ : Function.Injective ((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K)) :=
      (algebraMap K (AlgebraicClosure K)).injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
    obtain ⟨h1, h2⟩ := hT (AlgebraicClosure K) ((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K)) hβ
      (((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K)).comp τ)
    have hiff : (((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K)).comp τ) H.rt =
        ((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K)) ρ ↔ τ H.rt = ρ := hβ.eq_iff
    split_ifs with hτ
    · exact finrank_eigenSub F T.t.act r hr (algebraMap K (AlgebraicClosure K)) ((algebraMap (𝓞 K) K).comp τ)
        (h1 (hiff.mpr hτ))
    · exact finrank_eigenSub F T.t.act r hr (algebraMap K (AlgebraicClosure K)) ((algebraMap (𝓞 K) K).comp τ)
        (h2 (fun h => hτ (hiff.mp h)))
  have hfun : (fun τ : 𝓞 E →+* 𝓞 K => Submodule.span K (F.eigLat T.t.act τ : Set (Fin F.P₀.g → K))) =
      fun τ => EigenSplit.eigenSub r ((algebraMap (𝓞 K) K).comp τ) := funext hspan
  obtain ⟨hpart, hc1, hc2⟩ := card_half H hs hρ
  have hsum : ∑ τ : 𝓞 E →+* 𝓞 K, (if τ H.rt = ρ then p else q) = Module.finrank ℚ E / 2 * (p + q) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    have e1 : (Finset.univ.filter fun τ : 𝓞 E →+* 𝓞 K => τ H.rt = ρ).card = Module.finrank ℚ E / 2 := by
      rw [← hc1, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have e2 : (Finset.univ.filter fun τ : 𝓞 E →+* 𝓞 K => ¬ τ H.rt = ρ).card = Module.finrank ℚ E / 2 := by
      rw [← hc2, Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext τ
      simp [hpart τ]
    rw [e1, e2]
    ring
  have hdim : Module.finrank K (Fin F.P₀.g → K) =
      ∑ τ : 𝓞 E →+* 𝓞 K, Module.finrank K (EigenSplit.eigenSub r ((algebraMap (𝓞 K) K).comp τ)) := by
    rw [(EigenSplit.eigenEquiv hsplit r).finrank_eq, Module.finrank_pi_fintype]
  have hg : F.P₀.g = T.g := F.fib.1
  refine ⟨?_, ?_, ?_, ?_, hc1, hc2⟩
  · intro τ
    unfold latRank
    rw [hspan, hrank]
  · rw [hfun]
    exact hint.submodule_iSupIndep
  · rw [hfun]
    exact hint.submodule_iSup_eq_top
  · calc T.g = F.P₀.g := hg.symm
      _ = Module.finrank K (Fin F.P₀.g → K) := (Module.finrank_fin_fun K).symm
      _ = ∑ τ : 𝓞 E →+* 𝓞 K, (if τ H.rt = ρ then p else q) := by
        rw [hdim]
        exact Finset.sum_congr rfl fun τ _ => hrank τ
      _ = Module.finrank ℚ E / 2 * (p + q) := hsum

end GlobalTheory.CM.EigDec
