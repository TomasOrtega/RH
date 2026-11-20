import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PrimAn

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.KappaAn

/- English proof (translation)
Use `⟨(Scheme.stalkClosedPointTo j).hom.toMonoidHom.comp (Units.coeHom _), fun X r U h a => ?_⟩` and prove the remaining obligations. Establish `h' : ⊤ ≤ j ⁻¹ᵁ (r ⁻¹ᵁ U)` using `(top_le_preimage_iff_mem j _).2 h`. Rewrite using `[← GlobalTheory.valAt'_comp, valAt'_eq_valAt j h']`. Express the relevant statement in the definitionally equal form `(Scheme.stalkClosedPointTo j).hom (gm r _ U a).val = _`. Rewrite using `[gm_val r _ U h]`.

Use `Scheme.germ_stalkClosedPointTo j (r ⁻¹ᵁ U) h` as an intermediate fact. Conclude with `congrArg (fun q => q.hom ((r.app U).hom a.val)) this`.
-/
theorem exists_ev {Y : Scheme.{0}} (j : Sp ℂ ⟶ Y) :
    ∃ e : (Y.presheaf.stalk (j (IsLocalRing.closedPoint ℂ)))ˣ →* ℂ, ∀ (X : Scheme.{0}) (r : Y ⟶ X) (U : X.Opens),
      r (j (IsLocalRing.closedPoint ℂ)) ∈ U → ∀ a : Γ(X, U)ˣ,
        e (gm r (j (IsLocalRing.closedPoint ℂ)) U a) = valAt' (j ≫ r) U a.val := by
  refine ⟨(Scheme.stalkClosedPointTo j).hom.toMonoidHom.comp (Units.coeHom _), fun X r U h a => ?_⟩
  have h' : ⊤ ≤ j ⁻¹ᵁ (r ⁻¹ᵁ U) := (top_le_preimage_iff_mem j _).2 h
  rw [← GlobalTheory.valAt'_comp, valAt'_eq_valAt j h']
  change (Scheme.stalkClosedPointTo j).hom (gm r _ U a).val = _
  rw [gm_val r _ U h]
  have := Scheme.germ_stalkClosedPointTo j (r ⁻¹ᵁ U) h
  exact congrArg (fun q => q.hom ((r.app U).hom a.val)) this

variable {O : Type} [CommRing O] [StarRing O] [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {D₀ : Out.DegPre ℂ} [Module O D₀.X] {oa : D₀.OAct O} (d : GtDict D₀ oa)

/- English proof (translation)
Establish `h : ∀ k : ℕ, d.u.ex (k • d.A.ct y) = D₀.c (d.eX y) ^ k` using `fun k => by`. Proceed by induction on `k with`. Consider the case `zero => rw [zero_nsmul, pow_zero]`. Conclude with `(d.u.ker 0).2 (zero_mem _)`. Consider the case `succ k ih => rw [succ_nsmul, d.u.ex_add, ih, d.ex_ct, pow_succ]`.

Rewrite using `[← h, d.u.ker, d.lam_eq]`.
-/
theorem pow_eq_one_iff (n : ℕ) (y : d.A.X) : D₀.c (d.eX y) ^ n = 1 ↔ n • d.A.ct y ∈ d.A.abelian₂ := by
  have h : ∀ k : ℕ, d.u.ex (k • d.A.ct y) = D₀.c (d.eX y) ^ k := fun k => by
    induction k with
    | zero => rw [zero_nsmul, pow_zero]; exact (d.u.ker 0).2 (zero_mem _)
    | succ k ih => rw [succ_nsmul, d.u.ex_add, ih, d.ex_ct, pow_succ]
  rw [← h, d.u.ker, d.lam_eq]

omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

/- English proof (translation)
Establish `h1` using `A.H_conj l m`. Establish `h2 : A.H m l = (A.H l m).re - (A.H l m).im * Complex.I`. Apply the tactic sequence `rw [← h1]; apply Complex.ext <;> simp`. Establish `h3` using `Complex.re_add_im (A.H l m)`. Simplify using `only [AnArc.ah, AnArc.H_zero_left, mul_zero, zero_add, A.chi_add, ← A.H_def, Submodule.coe_add, A.H_add_left, A.H_add_right]`.

Establish `: Complex.exp (Real.pi * Complex.I * ((A.H l m).im : ℂ)) * Complex.exp (Real.pi / 2 * (A.H l l + A.H l m + (A.H m l + A.H m m))) = Complex.exp (Real.pi / 2 * A.H l l) * Complex.exp (Real.pi / 2 * A.H m m) * Complex.exp (Real.pi * A.H l m)`. Simplify using `only [← Complex.exp_add]`. Use `congr 1`. Rewrite using `[h2]`. Take the linear combination `(Real.pi / 2 : ℂ) * h3`.

Take the linear combination `A.chi l * A.chi m * this`.
-/
theorem ah_ratio (A : AnArc O) (l m : A.abelian₂) :
    A.ah (l + m) 0 = A.ah l 0 * A.ah m 0 * Complex.exp (Real.pi * A.H l m) := by
  have h1 := A.H_conj l m
  have h2 : A.H m l = (A.H l m).re - (A.H l m).im * Complex.I := by
    rw [← h1]; apply Complex.ext <;> simp
  have h3 := Complex.re_add_im (A.H l m)
  simp only [AnArc.ah, AnArc.H_zero_left, mul_zero, zero_add, A.chi_add, ← A.H_def, Submodule.coe_add,
    A.H_add_left, A.H_add_right]
  have : Complex.exp (Real.pi * Complex.I * ((A.H l m).im : ℂ)) *
      Complex.exp (Real.pi / 2 * (A.H l l + A.H l m + (A.H m l + A.H m m))) =
      Complex.exp (Real.pi / 2 * A.H l l) * Complex.exp (Real.pi / 2 * A.H m m) *
        Complex.exp (Real.pi * A.H l m) := by
    simp only [← Complex.exp_add]
    congr 1
    rw [h2]
    linear_combination (Real.pi / 2 : ℂ) * h3
  linear_combination A.chi l * A.chi m * this

/- English proof (translation)
Set `p : (Out.TK ℂ).left` to `Out.jFK (R := ℂ) ℂ (IsLocalRing.closedPoint ℂ)`. Take `⟨e, he⟩ : ∃ e : ((Out.TK ℂ).left.presheaf.stalk p)ˣ →* ℂ, ∀ (X : Scheme.{0}) (r : (Out.TK ℂ).left ⟶ X) (U : X.Opens), r p ∈ U → ∀ a : Γ(X, U)ˣ, e (gm r p U a) = valAt' (Out.jFK (R` from `ℂ) ℂ ≫ r) U a.val := exists_ev (Y := (Out.TK ℂ).left) (Out.jFK (R := ℂ) ℂ)`. Use `choose J hJ using fun q : (Out.TK ℂ).left ⟶ D₀.P.A.left => exists_chart D₀.P.isLB (q p)`. Establish `hG : Good D₀.P.L p J` using `hJ`. Set `z₀ : (Out.TK ℂ).left ⟶ D₀.P.A.left` to `(toUnit (Out.TK ℂ)).left ≫ eSec D₀.P.A`.

Establish `hz : Out.jFK (R` using `ℂ) ℂ ≫ (toUnit (Out.TK ℂ)).left = 𝟙 (Sp ℂ) := jFK_comp_jK_complex`. Establish `h0 : ⊤ ≤ (d.u.ex 0).left ⁻¹ᵁ D₀.P.L.U (J z₀)`. Establish `: (d.u.ex 0).left = Out.jFK (R` using `ℂ) ℂ ≫ z₀ := by`. Rewrite using `[d.ex_zero, ← Category.assoc, hz]`. Conclude with `(Category.id_comp _).symm`.

Rewrite using `[this]`. Conclude with `(top_le_preimage_iff_mem _ _).2 (hJ z₀)`. Establish `f0` using `d.u.fr_ne _ _ h0`. Establish `hψ : ∀ (x : d.A.X) (l : d.A.abelian₂), d.A.ct x = l → e (val (D₀.psi (d.eX x)) (𝟙 _) p J) = d.A.psi x * d.A.ah l 0 * (d.u.fr (J z₀) 0)⁻¹` using `fun x l hl => by`. Establish `h1 : D₀.c (d.eX x) = η[D₀.P.A]`.

Rewrite using `[← d.ex_ct, hl, ← d.ex_zero, ← d.ex_add_lam 0 l, zero_add]`. Establish `h2 : Out.ptK (D₀.c (d.eX x)) = z₀` using `by rw [h1]; rfl`. Establish `h3 : ⊤ ≤ (d.u.ex (d.A.ct x)).left ⁻¹ᵁ D₀.P.L.U (J z₀)` using `by rw [d.ex_ct, h1, ← d.ex_zero]; exact h0`. Rewrite using `[val_of _ _ _ _ (fun _ => J z₀) (fun _ => by rw [Category.id_comp, h2])]`. Establish `hm : (𝟙 (Out.TK ℂ).left : _ ⟶ _) p ∈ LB.wchart D₀.P.L (fun _ : PUnit => Out.ptK (D₀.c (d.eX x))) fun _ => J z₀`.

Rewrite using `[h2]`. Conclude with `Set.mem_iInter.2 fun _ => hJ z₀`. Use `(he _ _ _ hm _).trans ?_` and prove the remaining obligations. Rewrite using `[Category.comp_id]`. Use `(d.psi_val x (fun _ => J z₀) h3).trans ?_` and prove the remaining obligations.

Establish `h4` using `d.fr_eq_ah_mul l (J z₀) 0 h0`. Establish `h5` using `d.A.ah_ne_zero l 0`. Establish `h6` using `d.u.fr_ne _ _ h3`. Rewrite `h4` using `[zero_add]`. Rewrite `h6`, the goal using `[hl]`.

Rewrite using `[h4]`. Clear the denominators using the available nonvanishing facts. Establish `hρ : e (val D₀.rigK (𝟙 _) p J) = d.u.fr (J z₀) 0`. Establish `h1 : ⊤ ≤ (D₀.P.L.pull (eSec D₀.P.A)).U fun _ => J z₀`. Use `(top_le_wchart_iff D₀.P.L (fun _ : PUnit => eSec D₀.P.A) (fun _ => J z₀) (𝟙 (Sp ℂ))).2 fun _ => by` as an intermediate fact.

Rewrite `h0` using `[d.ex_zero]`. Conclude with `(Category.id_comp (eSec D₀.P.A)).symm ▸ h0`. Conclude with `this`. Rewrite using `[Out.DegPre.rigK, val_pull hG, val_of _ _ _ _ (fun _ => J z₀) (fun _ => by rw [Category.id_comp])]`. Use `(he _ _ _ (h1 trivial) _).trans ?_` and prove the remaining obligations.

Rewrite using `[Category.id_comp, hz]`. Conclude with `(d.isRig _ h1).symm`. Establish `hk` using `congrArg e ((TauTwist.unitAt_kappa hc (d.eX y) (d.eX y') hG).trans (TauTwist.val_tau D₀ _ _ _ hG))`. Establish `hl : ∀ x, d.A.ct (n • x) ∈ d.A.abelian₂` using `fun x => by`. Rewrite using `[map_nsmul]`.

Conclude with `(pow_eq_one_iff d n x).1 (hc _)`. Rewrite `hk` using `[map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, ← map_nsmul, ← map_nsmul, ← map_add, hρ, hψ (n • y) ⟨_, hl y⟩ rfl, hψ (n • y') ⟨_, hl y'⟩ rfl, hψ (n • y + n • y') (⟨_, hl y⟩ + ⟨_, hl y'⟩) (map_add _ _ _), ah_ratio, d.A.psi_add]`. Establish `hu : e (TauTwist.unitAt (𝟙 (Out.TK ℂ).left) p (TauTwist.kappa hc (d.eX y) (d.eX y'))) = algebraMap (FractionRing ℂ) ℂ (TauTwist.kappa hc (d.eX y) (d.eX y'))`. Generalize the expression as in `TauTwist.kappa hc (d.eX y) (d.eX y') = t`. Use `(he _ _ ⊤ trivial _).trans ?_` and prove the remaining obligations.

Use `GlobalTheory.valAt'_comp (𝟙 (Sp ℂ)) (Out.jFK (R := ℂ) ℂ) ⊤ (unitOn t).val` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Rewrite using `[Category.comp_id]`. Use `this.symm.trans ?_` and prove the remaining obligations. Conclude with `(congrArg (valAt' (𝟙 (Sp ℂ)) ⊤) (congrArg (fun e => e.hom t.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (FractionRing ℂ) ℂ)))).symm).trans (valAt'_id_top _)`.

Rewrite using `[← hu, hk, ← map_nsmul, ← map_nsmul]`. Use `(d.A.psi (n • y)).ne_zero` as an intermediate fact. Use `(d.A.psi (n • y')).ne_zero` as an intermediate fact. Use `d.A.ah_ne_zero ⟨_, hl y⟩ 0` as an intermediate fact. Use `d.A.ah_ne_zero ⟨_, hl y'⟩ 0` as an intermediate fact.

Clear the denominators using the available nonvanishing facts.
-/
theorem kappa_eq {n : ℕ} (hc : ∀ y, D₀.c y ^ n = 1) (y y' : d.A.X) :
    algebraMap (FractionRing ℂ) ℂ (TauTwist.kappa hc (d.eX y) (d.eX y')) =
      eTwoPi (d.A.T (n • y) (n • y')) * Complex.exp (Real.pi * d.A.H (n • d.A.ct y) (n • d.A.ct y')) := by
  let p : (Out.TK ℂ).left := Out.jFK (R := ℂ) ℂ (IsLocalRing.closedPoint ℂ)
  obtain ⟨e, he⟩ : ∃ e : ((Out.TK ℂ).left.presheaf.stalk p)ˣ →* ℂ, ∀ (X : Scheme.{0}) (r : (Out.TK ℂ).left ⟶ X)
      (U : X.Opens), r p ∈ U → ∀ a : Γ(X, U)ˣ, e (gm r p U a) = valAt' (Out.jFK (R := ℂ) ℂ ≫ r) U a.val :=
    exists_ev (Y := (Out.TK ℂ).left) (Out.jFK (R := ℂ) ℂ)
  choose J hJ using fun q : (Out.TK ℂ).left ⟶ D₀.P.A.left => exists_chart D₀.P.isLB (q p)
  have hG : Good D₀.P.L p J := hJ
  let z₀ : (Out.TK ℂ).left ⟶ D₀.P.A.left := (toUnit (Out.TK ℂ)).left ≫ eSec D₀.P.A
  have hz : Out.jFK (R := ℂ) ℂ ≫ (toUnit (Out.TK ℂ)).left = 𝟙 (Sp ℂ) := jFK_comp_jK_complex
  have h0 : ⊤ ≤ (d.u.ex 0).left ⁻¹ᵁ D₀.P.L.U (J z₀) := by
    have : (d.u.ex 0).left = Out.jFK (R := ℂ) ℂ ≫ z₀ := by
      rw [d.ex_zero, ← Category.assoc, hz]; exact (Category.id_comp _).symm
    rw [this]
    exact (top_le_preimage_iff_mem _ _).2 (hJ z₀)
  have f0 := d.u.fr_ne _ _ h0
  have hψ : ∀ (x : d.A.X) (l : d.A.abelian₂), d.A.ct x = l →
      e (val (D₀.psi (d.eX x)) (𝟙 _) p J) = d.A.psi x * d.A.ah l 0 * (d.u.fr (J z₀) 0)⁻¹ := fun x l hl => by
    have h1 : D₀.c (d.eX x) = η[D₀.P.A] := by
      rw [← d.ex_ct, hl, ← d.ex_zero, ← d.ex_add_lam 0 l, zero_add]
    have h2 : Out.ptK (D₀.c (d.eX x)) = z₀ := by rw [h1]; rfl
    have h3 : ⊤ ≤ (d.u.ex (d.A.ct x)).left ⁻¹ᵁ D₀.P.L.U (J z₀) := by rw [d.ex_ct, h1, ← d.ex_zero]; exact h0
    rw [val_of _ _ _ _ (fun _ => J z₀) (fun _ => by rw [Category.id_comp, h2])]
    have hm : (𝟙 (Out.TK ℂ).left : _ ⟶ _) p ∈
        LB.wchart D₀.P.L (fun _ : PUnit => Out.ptK (D₀.c (d.eX x))) fun _ => J z₀ := by
      rw [h2]; exact Set.mem_iInter.2 fun _ => hJ z₀
    refine (he _ _ _ hm _).trans ?_
    rw [Category.comp_id]
    refine (d.psi_val x (fun _ => J z₀) h3).trans ?_
    have h4 := d.fr_eq_ah_mul l (J z₀) 0 h0
    have h5 := d.A.ah_ne_zero l 0
    have h6 := d.u.fr_ne _ _ h3
    rw [zero_add] at h4
    rw [hl] at h6 ⊢
    rw [h4]
    field_simp
  have hρ : e (val D₀.rigK (𝟙 _) p J) = d.u.fr (J z₀) 0 := by
    have h1 : ⊤ ≤ (D₀.P.L.pull (eSec D₀.P.A)).U fun _ => J z₀ := by
      have := (top_le_wchart_iff D₀.P.L (fun _ : PUnit => eSec D₀.P.A) (fun _ => J z₀) (𝟙 (Sp ℂ))).2 fun _ => by
        rw [d.ex_zero] at h0
        exact (Category.id_comp (eSec D₀.P.A)).symm ▸ h0
      exact this
    rw [Out.DegPre.rigK, val_pull hG, val_of _ _ _ _ (fun _ => J z₀) (fun _ => by rw [Category.id_comp])]
    refine (he _ _ _ (h1 trivial) _).trans ?_
    rw [Category.id_comp, hz]
    exact (d.isRig _ h1).symm
  have hk := congrArg e ((TauTwist.unitAt_kappa hc (d.eX y) (d.eX y') hG).trans (TauTwist.val_tau D₀ _ _ _ hG))
  have hl : ∀ x, d.A.ct (n • x) ∈ d.A.abelian₂ := fun x => by
    rw [map_nsmul]; exact (pow_eq_one_iff d n x).1 (hc _)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, ← map_nsmul, ← map_nsmul, ← map_add, hρ,
    hψ (n • y) ⟨_, hl y⟩ rfl, hψ (n • y') ⟨_, hl y'⟩ rfl,
    hψ (n • y + n • y') (⟨_, hl y⟩ + ⟨_, hl y'⟩) (map_add _ _ _), ah_ratio, d.A.psi_add] at hk
  have hu : e (TauTwist.unitAt (𝟙 (Out.TK ℂ).left) p (TauTwist.kappa hc (d.eX y) (d.eX y'))) =
      algebraMap (FractionRing ℂ) ℂ (TauTwist.kappa hc (d.eX y) (d.eX y')) := by
    generalize TauTwist.kappa hc (d.eX y) (d.eX y') = t
    refine (he _ _ ⊤ trivial _).trans ?_
    have := GlobalTheory.valAt'_comp (𝟙 (Sp ℂ)) (Out.jFK (R := ℂ) ℂ) ⊤ (unitOn t).val
    rw [Category.id_comp] at this
    rw [Category.comp_id]
    refine this.symm.trans ?_
    exact (congrArg (valAt' (𝟙 (Sp ℂ)) ⊤) (congrArg (fun e => e.hom t.val)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (FractionRing ℂ) ℂ)))).symm).trans
      (valAt'_id_top _)
  rw [← hu, hk, ← map_nsmul, ← map_nsmul]
  have := (d.A.psi (n • y)).ne_zero
  have := (d.A.psi (n • y')).ne_zero
  have := d.A.ah_ne_zero ⟨_, hl y⟩ 0
  have := d.A.ah_ne_zero ⟨_, hl y'⟩ 0
  field_simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hc, hk⟩`. Use `⟨fun y => (pow_eq_one_iff d n y).1 (hc _), fun y y' => ?_⟩` and prove the remaining obligations. Rewrite using `[← kappa_eq d hc, hk]`. Conclude with `map_one _`.

Introduce and unpack `⟨h₁, h₂⟩`. Establish `hc : ∀ y, D₀.c y ^ n = 1` using `fun y => by`. Take `⟨y, rfl⟩` from `d.eX.surjective y`. Conclude with `(pow_eq_one_iff d n y).2 (h₁ y)`. Use `⟨hc, fun y y' => ?_⟩` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `d.eX.surjective y`. Take `⟨y', rfl⟩` from `d.eX.surjective y'`. Conclude with `Units.ext ((algebraMap (FractionRing ℂ) ℂ).injective (((kappa_eq d hc y y').trans (h₂ y y')).trans (map_one _).symm))`.
-/
theorem tauCan_iff (n : ℕ) : TauCan D₀ n ↔
    (∀ y, n • d.A.ct y ∈ d.A.abelian₂) ∧
      ∀ y y', eTwoPi (d.A.T (n • y) (n • y')) * Complex.exp (Real.pi * d.A.H (n • d.A.ct y) (n • d.A.ct y')) = 1 := by
  constructor
  · rintro ⟨hc, hk⟩
    refine ⟨fun y => (pow_eq_one_iff d n y).1 (hc _), fun y y' => ?_⟩
    rw [← kappa_eq d hc, hk]
    exact map_one _
  · rintro ⟨h₁, h₂⟩
    have hc : ∀ y, D₀.c y ^ n = 1 := fun y => by
      obtain ⟨y, rfl⟩ := d.eX.surjective y
      exact (pow_eq_one_iff d n y).2 (h₁ y)
    refine ⟨hc, fun y y' => ?_⟩
    obtain ⟨y, rfl⟩ := d.eX.surjective y
    obtain ⟨y', rfl⟩ := d.eX.surjective y'
    exact Units.ext ((algebraMap (FractionRing ℂ) ℂ).injective (((kappa_eq d hc y y').trans (h₂ y y')).trans
      (map_one _).symm))

end GlobalTheory.KappaAn

/- English proof (translation)
Introduce `E _ _ _ H Dw l c _ _ O _ β b a Λ n`. Conclude with `@GlobalTheory.KappaAn.tauCan_iff (𝓞 E) _ H.starRing _ _ a.D₀ a.mod a.oa Λ.toGtDict n`.
-/
theorem GlobalTheory.KappaAn.tauCan_iff_normAn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (b : O →+* ℂ) (a : ArcIn Dw l β ℂ b) (Λ : GtAn₀ a) (n : ℕ), letI := H.starRing; (TauCan a.D₀ n ↔ NormAn Λ.A n) := by
  intro E _ _ _ H Dw l c _ _ O _ β b a Λ n
  exact @GlobalTheory.KappaAn.tauCan_iff (𝓞 E) _ H.starRing _ _ a.D₀ a.mod a.oa Λ.toGtDict n
