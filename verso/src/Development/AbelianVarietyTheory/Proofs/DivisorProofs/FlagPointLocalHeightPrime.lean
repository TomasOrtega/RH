import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdlCutProj
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

section SlopeTestRemainingChoices

open GlobalTheory.ShFam.CoordUniq GlobalTheory.ShFam.Pad.Guard GlobalTheory.Cartier

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
private theorem sp_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
Take `rfl : φ₁ = φ₂` from `RingHom.ext fun a => hι ((RingHom.congr_fun h₁.2.1 a).symm.trans (RingHom.congr_fun h₂.2.1 a))`. Take `⟨k₁, hk₁⟩` from `f₁.exists_isMap _ h₁.2.1 h₁.1`. Take `⟨k₂, hk₂⟩` from `f₂.exists_isMap _ h₁.2.1 h₁.1`. Take `⟨q₁, hq₁⟩` from `f₁.exists_isMap _ b.2.1 b.1`. Take `⟨q₂, hq₂⟩` from `f₂.exists_isMap _ b.2.1 b.1`.

Establish `e1 (τ i d) : k₂.co f₀ τ d i = ∑ j, k₁.co f₀ τ j i * ι (f₂.co f₁ τ d j)`. Rewrite using `[← k₂.co_mul k₁, hk₂.co τ hk₁ h₁.1, Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Establish `hM (τ d i) (h : i < d) : f₂.co f₁ τ d i = 0` using `hι ((tri_of_mul (M := fun i a => ι (f₂.co f₁ τ a i)) (fun i a => (h₂.co τ hk₂).1 a i) (fun i a' => (h₁.co τ hk₁).1 a' i) (fun i => (h₁.co τ hk₁).2 i ▸ (t₁ τ i).ne_zero) (e1 τ) i d h).trans (map_zero _).symm)`. Establish `hT (τ) (a i) (h : i < a) : q₂.co g τ a i = 0`.

Rewrite using `[← q₂.co_mul q₁, hq₂.co τ hq₁ b.1, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Break down `lt_or_ge j a with hj | hj` into its components or cases. Rewrite using `[Matrix.map_apply, hM τ a j hj, map_zero, zero_mul]`. Rewrite using `[(b.co τ hq₁).1 j i (h.trans_le hj), mul_zero]`.

Establish `hu (τ i) : q₂.co g τ i i ≠ 0`. Use `q₂.isUnit_det_co g τ` as an intermediate fact. Rewrite `this` using `[Matrix.det_of_upperTriangular (M := q₂.co g τ) fun _ _ h => hT τ _ _ h]`. Conclude with `Finset.prod_ne_zero_iff.1 this.ne_zero i (Finset.mem_univ i)`. Use `⟨fun τ i => Units.mk0 _ (hu τ i), b.1, b.2.1, fun τ i => ⟨fun a => q₂.co g τ a i, rfl, fun a ha => hT τ a i ha, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[← funext (hq₂ τ)]`. Conclude with `q₂.co_spec g τ i`.
-/
private theorem tri_swap {R : Type} [CommRing R]
    {φ₁ φ₂ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ : EigFrame Z φ₁ x) (f₂ : EigFrame Z φ₂ x) {K : Type} [Field K] {ι : R →+* K} (hι : Function.Injective ι)
    {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} {f₀ : EigFrame Z φ₀ x₀} {t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (h₁ : f₁.Tri ι f₀ t₁) (h₂ : f₂.Tri ι f₀ t₂) {k : Type} [Field k] {ψ : R →+* k} {φ' : c.F →+* k}
    {x' : Sp k ⟶ Z.X} {g : EigFrame Z φ' x'} {s₁ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ} (b : f₁.Tri ψ g s₁) :
    ∃ s₂, f₂.Tri ψ g s₂ := by
  obtain rfl : φ₁ = φ₂ := RingHom.ext fun a => hι ((RingHom.congr_fun h₁.2.1 a).symm.trans (RingHom.congr_fun h₂.2.1 a))
  obtain ⟨k₁, hk₁⟩ := f₁.exists_isMap _ h₁.2.1 h₁.1
  obtain ⟨k₂, hk₂⟩ := f₂.exists_isMap _ h₁.2.1 h₁.1
  obtain ⟨q₁, hq₁⟩ := f₁.exists_isMap _ b.2.1 b.1
  obtain ⟨q₂, hq₂⟩ := f₂.exists_isMap _ b.2.1 b.1
  have e1 (τ i d) : k₂.co f₀ τ d i = ∑ j, k₁.co f₀ τ j i * ι (f₂.co f₁ τ d j) := by
    rw [← k₂.co_mul k₁, hk₂.co τ hk₁ h₁.1, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hM (τ d i) (h : i < d) : f₂.co f₁ τ d i = 0 := hι ((tri_of_mul
    (M := fun i a => ι (f₂.co f₁ τ a i)) (fun i a => (h₂.co τ hk₂).1 a i)
    (fun i a' => (h₁.co τ hk₁).1 a' i) (fun i => (h₁.co τ hk₁).2 i ▸ (t₁ τ i).ne_zero) (e1 τ) i d h).trans
      (map_zero _).symm)
  have hT (τ) (a i) (h : i < a) : q₂.co g τ a i = 0 := by
    rw [← q₂.co_mul q₁, hq₂.co τ hq₁ b.1, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases lt_or_ge j a with hj | hj
    · rw [Matrix.map_apply, hM τ a j hj, map_zero, zero_mul]
    · rw [(b.co τ hq₁).1 j i (h.trans_le hj), mul_zero]
  have hu (τ i) : q₂.co g τ i i ≠ 0 := by
    have := q₂.isUnit_det_co g τ
    rw [Matrix.det_of_upperTriangular (M := q₂.co g τ) fun _ _ h => hT τ _ _ h] at this
    exact Finset.prod_ne_zero_iff.1 this.ne_zero i (Finset.mem_univ i)
  refine ⟨fun τ i => Units.mk0 _ (hu τ i), b.1, b.2.1, fun τ i => ⟨fun a => q₂.co g τ a i, rfl, fun a ha => hT τ a i ha, ?_⟩⟩
  rw [← funext (hq₂ τ)]
  exact q₂.co_spec g τ i

/- English proof (translation)
Break down `st with ⟨τ, k⟩ | k` into its components or cases. Distinguish the cases in `hk : k < Dw.mult τ`. Simplify using `only [letterOf, stepNorm, dif_pos hk, Option.elim]`. Rewrite using `[grNorm_tri (f.tan τ) (d := fun i => d ⟨τ, i⟩) (fun i => hd _) (h τ)]`. Simplify using `[letterOf, stepNorm, hk]`.

Distinguish the cases in `hk : k < (letters Dw).length`. Take `⟨i1, c1⟩` from `GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame E H Dw l c Z.X Z.t C φ x f.v ⟨fun τ i => ⟨f.tan τ i, f.eig τ i⟩, f.basis⟩`. Establish `e : letterOf Dw (.inr k) = some ((letters Dw).get ⟨k, hk⟩)` using `List.getElem?_eq_getElem hk`. Simplify using `only [e, stepNorm, dif_pos hk, Option.elim]`. Rewrite using `[grNorm_tri (u := fun i => f.v ((letters Dw).get i).1 ((letters Dw).get i).2) (fun i => f.tan _ _) (d := fun i => d ((letters Dw).get i)) (fun i => hd _) (fun j => by`.

Take `⟨cf, e1, e2, e3⟩` from `h ((letters Dw).get j).1 ((letters Dw).get j).2`. Take `⟨cg, a1, a2, a3⟩` from `c1 j cf _ e2 e3`. Conclude with `⟨cg, a2.trans e1, a1, a3⟩)]`. Establish `e : letterOf Dw (.inr k) = none` using `List.getElem?_eq_none (not_lt.1 hk)`. Simplify using `[e, stepNorm, hk]`.
-/
private theorem stepNorm_change {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] {φ : c.F →+* C} {x : Sp C ⟶ Z.X} (f g : EigFrame Z φ x)
    {d : Pad.Letter Dw → C} (hd : ∀ z, d z ≠ 0)
    (h : ∀ τ i, ∃ cf : Fin (Dw.mult τ) → C, cf i = d ⟨τ, i⟩ ∧ (∀ k, i < k → cf k = 0) ∧
      IsCombAtG Z.t x (f.v τ) cf (g.v τ i)) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) :
    stepNorm Z.t x g.v st = (letterOf Dw st).elim 1 (fun z => ‖d z‖) * stepNorm Z.t x f.v st := by
  rcases st with ⟨τ, k⟩ | k
  · by_cases hk : k < Dw.mult τ
    · simp only [letterOf, stepNorm, dif_pos hk, Option.elim]
      rw [grNorm_tri (f.tan τ) (d := fun i => d ⟨τ, i⟩) (fun i => hd _) (h τ)]
    · simp [letterOf, stepNorm, hk]
  · by_cases hk : k < (letters Dw).length
    · obtain ⟨i1, c1⟩ := GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame E H Dw l c Z.X Z.t C φ x f.v
        ⟨fun τ i => ⟨f.tan τ i, f.eig τ i⟩, f.basis⟩
      have e : letterOf Dw (.inr k) = some ((letters Dw).get ⟨k, hk⟩) := List.getElem?_eq_getElem hk
      simp only [e, stepNorm, dif_pos hk, Option.elim]
      rw [grNorm_tri (u := fun i => f.v ((letters Dw).get i).1 ((letters Dw).get i).2) (fun i => f.tan _ _)
        (d := fun i => d ((letters Dw).get i)) (fun i => hd _) (fun j => by
          obtain ⟨cf, e1, e2, e3⟩ := h ((letters Dw).get j).1 ((letters Dw).get j).2
          obtain ⟨cg, a1, a2, a3⟩ := c1 j cf _ e2 e3
          exact ⟨cg, a2.trans e1, a1, a3⟩)]
    · have e : letterOf Dw (.inr k) = none := List.getElem?_eq_none (not_lt.1 hk)
      simp [e, stepNorm, hk]

/- English proof (translation)
Rewrite `hA`, the goal using `[h]`. Rewrite using `[Real.log_mul (left_ne_zero_of_mul hA) (right_ne_zero_of_mul hA)]`. Apply the tactic sequence `cases o <;> simp`.
-/
private theorem log_change {A B : ℝ} {o : Option (Pad.Letter Dw)} {N : Pad.Letter Dw → ℝ}
    (h : A = o.elim 1 N * B) (hA : A ≠ 0) : Real.log A = o.elim 0 (fun z => Real.log (N z)) + Real.log B := by
  rw [h] at hA ⊢
  rw [Real.log_mul (left_ne_zero_of_mul hA) (right_ne_zero_of_mul hA)]
  cases o <;> simp

/- English proof (translation)
Simplify using `only [expo, Finsupp.sum, Int.cast_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Break down `letterOf Dw a.2.2 with _ | z` into its components or cases. Simplify using the standard rewrite rules.

Rewrite using `[Finset.sum_eq_single z (fun b _ hb => by simp [hb.symm]) (by simp)]`. Simplify using the standard rewrite rules.
-/
private theorem sum_letters (w : Pad.Sym E →₀ ℤ) (L : Pad.Letter Dw → ℝ) :
    ∑ a ∈ w.support, (w a : ℝ) * (letterOf Dw a.2.2).elim 0 L = ∑ z, (expo Dw w z : ℝ) * L z := by
  classical
  simp only [expo, Finsupp.sum, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases letterOf Dw a.2.2 with _ | z
  · simp
  · rw [Finset.sum_eq_single z (fun b _ hb => by simp [hb.symm]) (by simp)]
    simp

/- English proof (translation)
Take `⟨s₂, b₂⟩` from `tri_swap f₁ f₂ hι h₁ h₂ b`. Take `⟨u, hu⟩` from `exists_unit_ratio f₂ f₁ hι h₂ h₁`. Use `⟨s₂, r₁ * ((∏ z : Pad.Letter Dw, u z.1 z.2 ^ n z : Rˣ) : R), b₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hr, mul_assoc]`. Use `congr 1`.

Simplify using `only [hu _ _ _ _ h₂ h₁, mul_zpow, Finset.prod_mul_distrib, ← map_zpow, ← map_prod]`. Both sides reduce to the same expression. Establish `hs : Units.map (ψ : R →* k) (∏ z : Pad.Letter Dw, u z.1 z.2 ^ n z) * ∏ z : Pad.Letter Dw, s₂ z.1 z.2 ^ (-n z) = ∏ z : Pad.Letter Dw, s₁ z.1 z.2 ^ (-n z)`. Simplify using `only [hu _ _ _ _ b₂ b, mul_zpow, map_prod, map_zpow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun z _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_left_comm, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]`. Rewrite using `[map_mul, mul_assoc, ← hs]`. Both sides reduce to the same expression.
-/
private theorem coord_move {R : Type} [CommRing R]
    [IsLocalRing R] {φ₁ φ₂ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ : EigFrame Z φ₁ x) (f₂ : EigFrame Z φ₂ x) {K : Type} [Field K] {ι : R →+* K} (hι : Function.Injective ι)
    {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} {f₀ : EigFrame Z φ₀ x₀} {t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (h₁ : f₁.Tri ι f₀ t₁) (h₂ : f₂.Tri ι f₀ t₂) {k : Type} [Field k] {ψ : R →+* k} {φ' : c.F →+* k}
    {x' : Sp k ⟶ Z.X} {g : EigFrame Z φ' x'} {s₁ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ} (b : f₁.Tri ψ g s₁)
    (n : Pad.Letter Dw → ℤ) {σ : K} {r₁ : R} (hr : ι r₁ = σ * ((∏ z : Pad.Letter Dw, t₁ z.1 z.2 ^ n z : Kˣ) : K)) :
    ∃ (s₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ) (r₂ : R), f₂.Tri ψ g s₂ ∧
      ι r₂ = σ * ((∏ z : Pad.Letter Dw, t₂ z.1 z.2 ^ n z : Kˣ) : K) ∧
      ψ r₁ * ((∏ z : Pad.Letter Dw, s₁ z.1 z.2 ^ (-n z) : kˣ) : k) =
        ψ r₂ * ((∏ z : Pad.Letter Dw, s₂ z.1 z.2 ^ (-n z) : kˣ) : k) := by
  obtain ⟨s₂, b₂⟩ := tri_swap f₁ f₂ hι h₁ h₂ b
  obtain ⟨u, hu⟩ := exists_unit_ratio f₂ f₁ hι h₂ h₁
  refine ⟨s₂, r₁ * ((∏ z : Pad.Letter Dw, u z.1 z.2 ^ n z : Rˣ) : R), b₂, ?_, ?_⟩
  · rw [map_mul, hr, mul_assoc]
    congr 1
    simp only [hu _ _ _ _ h₂ h₁, mul_zpow, Finset.prod_mul_distrib, ← map_zpow, ← map_prod]
    rfl
  · have hs : Units.map (ψ : R →* k) (∏ z : Pad.Letter Dw, u z.1 z.2 ^ n z) *
        ∏ z : Pad.Letter Dw, s₂ z.1 z.2 ^ (-n z) = ∏ z : Pad.Letter Dw, s₁ z.1 z.2 ^ (-n z) := by
      simp only [hu _ _ _ _ b₂ b, mul_zpow, map_prod, map_zpow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun z _ => ?_
      rw [mul_left_comm, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
    rw [map_mul, mul_assoc, ← hs]
    rfl

/- English proof (translation)
Establish `hx : spMap J ≫ x = spMap (J.comp ψ) ≫ x₀`. Rewrite using `[b₂.1, ← Category.assoc, sp_comp']`. Take `⟨f', hf'⟩` from `f₂.exists_isMap (J.comp ψ) (φ' := J.comp φ) (by rw [b₂.2.1, RingHom.comp_assoc]) hx`. Take `⟨g', hg'⟩` from `g.exists_isMap J rfl rfl`. Establish `key` using `stepNorm_change f' g' (d := fun z => J (s z.1 z.2)) (fun z => (map_ne_zero _).2 (Units.ne_zero _)) (fun τ i => by`.

Take `⟨cf, e1, e2, e3⟩` from `b₂.2.2 τ i`. Use `⟨fun a => J (cf a), congrArg J e1, fun a ha => (congrArg J (e2 a ha)).trans (map_zero _), ?_⟩` and prove the remaining obligations. Use `GlobalTheory.GradedPieces.comb_map J rfl e3` as an intermediate fact. Simplify using `only [GlobalTheory.GradedPieces.dual_comp] at this`. Rewrite using `[hg' τ i, funext (hf' τ)]`.

Conclude with `this)`. Establish `ef : (fun τ i => spMap (dualMap (J.comp ψ)) ≫ f₂.v τ i) = f'.v`. Use function extensionality and compare the values at `fun τ => funext fun i => (hf' τ i).symm`. Establish `eg : (fun τ i => spMap (dualMap J) ≫ g.v τ i) = g'.v`. Use function extensionality and compare the values at `fun τ => funext fun i => (hg' τ i).symm`.

Rewrite `hn` using `[eg]`. Rewrite using `[← hx, ef, eg, Finsupp.sum, Finsupp.sum, Finset.sum_congr rfl fun a ha => by rw [hw a ha, lnStep_false], Finset.sum_congr (s₁ := w.support) (f := fun a => (w a : ℝ) * Real.log (stepNorm Z.t _ g'.v a.2.2)) rfl fun a ha => by rw [log_change (key a.2.2) (hn a ha)]]`. Simplify using `only [mul_add, Finset.sum_add_distrib, sum_letters]`. Establish `hr0 : J r ≠ 0` using `(map_ne_zero _).2 hr`. Establish `hs0 (z : Pad.Letter Dw) : ‖J (s z.1 z.2)‖ ≠ 0` using `norm_ne_zero_iff.2 ((map_ne_zero _).2 (Units.ne_zero _))`.

Simplify using `only [Units.coe_prod, Units.val_zpow_eq_zpow_val, map_mul, map_prod, map_zpow₀, norm_mul, norm_prod, norm_zpow]`. Rewrite using `[Real.log_mul (norm_ne_zero_iff.2 hr0) (Finset.prod_ne_zero_iff.2 fun z _ => zpow_ne_zero _ (hs0 z)), Real.log_prod fun z _ => zpow_ne_zero _ (hs0 z)]`. Simplify using `only [Real.log_zpow, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem core {R k C : Type} [CommRing R] [Field k]
    [NontriviallyNormedField C] [IsUltrametricDist C] {φ₂ : c.F →+* R} {x₀ : Sp R ⟶ Z.X} (f₂ : EigFrame Z φ₂ x₀)
    {φ : c.F →+* k} {x : Sp k ⟶ Z.X} (g : EigFrame Z φ x) {ψ : R →+* k} {s : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ}
    (b₂ : f₂.Tri ψ g s) (J : k →+* C) (p : ℕ) (w : Pad.Sym E →₀ ℤ)
    (hw : ∀ a ∈ w.support, a.1 p = false)
    (hn : ∀ a ∈ w.support, stepNorm Z.t (spMap J ≫ x) (fun τ i => spMap (dualMap J) ≫ g.v τ i) a.2.2 ≠ 0)
    {r : k} (hr : r ≠ 0) :
    Real.log ‖J r‖ + (w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap (J.comp ψ) ≫ x₀)
        (fun τ i => spMap (dualMap (J.comp ψ)) ≫ f₂.v τ i) p (a.1 p) a.2.2) =
      Real.log ‖J (r * ((∏ z : Pad.Letter Dw, s z.1 z.2 ^ (-expo Dw w z) : kˣ) : k))‖ +
        w.sum fun a n => (n : ℝ) *
          Real.log (stepNorm Z.t (spMap J ≫ x) (fun τ i => spMap (dualMap J) ≫ g.v τ i) a.2.2) := by
  have hx : spMap J ≫ x = spMap (J.comp ψ) ≫ x₀ := by
    rw [b₂.1, ← Category.assoc, sp_comp']
  obtain ⟨f', hf'⟩ := f₂.exists_isMap (J.comp ψ) (φ' := J.comp φ) (by rw [b₂.2.1, RingHom.comp_assoc]) hx
  obtain ⟨g', hg'⟩ := g.exists_isMap J rfl rfl
  have key := stepNorm_change f' g' (d := fun z => J (s z.1 z.2))
    (fun z => (map_ne_zero _).2 (Units.ne_zero _)) (fun τ i => by
      obtain ⟨cf, e1, e2, e3⟩ := b₂.2.2 τ i
      refine ⟨fun a => J (cf a), congrArg J e1, fun a ha => (congrArg J (e2 a ha)).trans (map_zero _), ?_⟩
      have := GlobalTheory.GradedPieces.comb_map J rfl e3
      simp only [GlobalTheory.GradedPieces.dual_comp] at this
      rw [hg' τ i, funext (hf' τ)]
      exact this)
  have ef : (fun τ i => spMap (dualMap (J.comp ψ)) ≫ f₂.v τ i) = f'.v :=
    funext fun τ => funext fun i => (hf' τ i).symm
  have eg : (fun τ i => spMap (dualMap J) ≫ g.v τ i) = g'.v :=
    funext fun τ => funext fun i => (hg' τ i).symm
  rw [eg] at hn
  rw [← hx, ef, eg, Finsupp.sum, Finsupp.sum, Finset.sum_congr rfl fun a ha => by rw [hw a ha, lnStep_false],
    Finset.sum_congr (s₁ := w.support) (f := fun a => (w a : ℝ) * Real.log (stepNorm Z.t _ g'.v a.2.2)) rfl
      fun a ha => by rw [log_change (key a.2.2) (hn a ha)]]
  simp only [mul_add, Finset.sum_add_distrib, sum_letters]
  have hr0 : J r ≠ 0 := (map_ne_zero _).2 hr
  have hs0 (z : Pad.Letter Dw) : ‖J (s z.1 z.2)‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero _).2 (Units.ne_zero _))
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, map_mul, map_prod, map_zpow₀, norm_mul, norm_prod, norm_zpow]
  rw [Real.log_mul (norm_ne_zero_iff.2 hr0) (Finset.prod_ne_zero_iff.2 fun z _ => zpow_ne_zero _ (hs0 z)),
    Real.log_prod fun z _ => zpow_ne_zero _ (hs0 z)]
  simp only [Real.log_zpow, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring

/- English proof (translation)
Establish `: CharZero c.F` using `RingHom.charZero c.F.val.toRingHom`. Take `⟨y₀, ψ, φ₁, f, t, t', r, h₁, h₂, h₃, h₄, rfl⟩` from `hco`. Establish `h0 : spMap ψ ≫ Y.Y.X.fromSpecStalk y₀ = spMap (Scheme.stalkClosedPointTo y).hom ≫ Y.Y.X.fromSpecStalk (below y)` using `h₁.symm.trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y).symm`. Establish `hE` using `stalk_ext (isLocalHom_of_algebraic φ₁ ψ) inferInstance h0`. Take `rfl : y₀ = below y` from `hE.1`.

Take `rfl` from `eq_of_heq hE.2`. Establish `hι` using `IsFractionRing.injective (Y.Y.X.presheaf.stalk (below y)) Y.Y.X.functionField`. Take `⟨s, r₂, b₂, hr, hb'⟩` from `coord_move f f₂ hι h₂ h h₃ _ h₄`. Establish `hP : ∀ s : Finset (Pad.Letter Dw), (∑ z ∈ s, n z • Y.gr z.1 z.2).IsEqn (below y) (∏ z ∈ s, t₂ z.1 z.2 ^ n z)` using `fun s => by classical`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simpa using CartierDiv.isEqn_zero (below y)`. Consider the case `insert z s hz ih => rw [Finset.sum_insert hz, Finset.prod_insert hz]`. Conclude with `((ht _ _).zsmul _).add ih`. Take `⟨u, hu, hu'⟩` from `(Base.isEqn_eqn (divOf Y n) (below y)).iff_unitAt.1 (hP Finset.univ)`. Take `rfl : u = r₂` from `hι (by rw [hu', hr, div_eq_inv_mul, Units.val_inv_eq_inv_val])`.

Use `⟨s, _, (hu.map (Scheme.stalkClosedPointTo y).hom).ne_zero, b₂, ?_, hb'⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, mul_comm, ← hr, Base.valAt_stalk]`.
-/
private theorem coord_at {F : Type} [Field F] [NumberField F]
    {e : F ≃+* c.F} (Y : FlagCpt Z e) {K : Type} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]
    {φ : c.F →+* K} {x : Sp K ⟶ Z.X} {g : EigFrame Z φ x} {y : Sp K ⟶ Y.Y.X} {n : Pad.Letter Dw → ℤ} {b : K}
    (hco : IsCoord Y y g n (((eqn (divOf Y n) (below y))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) b)
    {φ₂ : c.F →+* Y.Y.X.presheaf.stalk (below y)} (f₂ : EigFrame Z φ₂ (stalkPt Y.Y (below y) ≫ Y.π ≫ genι Z))
    {t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ}
    (h : f₂.Tri (algebraMap (Y.Y.X.presheaf.stalk (below y)) Y.Y.X.functionField) Y.f0 t₂)
    (ht : ∀ τ i, (Y.gr τ i).IsEqn (below y) (t₂ τ i)) :
    ∃ (s : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ) (r : K), r ≠ 0 ∧
      f₂.Tri (Scheme.stalkClosedPointTo y).hom g s ∧
      valAt y (((∏ z : Pad.Letter Dw, t₂ z.1 z.2 ^ n z) * (eqn (divOf Y n) (below y))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) = r ∧
      b = r * ((∏ z : Pad.Letter Dw, s z.1 z.2 ^ (-n z) : Kˣ) : K) := by
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨y₀, ψ, φ₁, f, t, t', r, h₁, h₂, h₃, h₄, rfl⟩ := hco
  have h0 : spMap ψ ≫ Y.Y.X.fromSpecStalk y₀ =
      spMap (Scheme.stalkClosedPointTo y).hom ≫ Y.Y.X.fromSpecStalk (below y) :=
    h₁.symm.trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y).symm
  have hE := stalk_ext (isLocalHom_of_algebraic φ₁ ψ) inferInstance h0
  obtain rfl : y₀ = below y := hE.1
  obtain rfl := eq_of_heq hE.2
  have hι := IsFractionRing.injective (Y.Y.X.presheaf.stalk (below y)) Y.Y.X.functionField
  obtain ⟨s, r₂, b₂, hr, hb'⟩ := coord_move f f₂ hι h₂ h h₃ _ h₄
  have hP : ∀ s : Finset (Pad.Letter Dw),
      (∑ z ∈ s, n z • Y.gr z.1 z.2).IsEqn (below y) (∏ z ∈ s, t₂ z.1 z.2 ^ n z) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using CartierDiv.isEqn_zero (below y)
    | insert z s hz ih => rw [Finset.sum_insert hz, Finset.prod_insert hz]; exact ((ht _ _).zsmul _).add ih
  obtain ⟨u, hu, hu'⟩ := (Base.isEqn_eqn (divOf Y n) (below y)).iff_unitAt.1 (hP Finset.univ)
  obtain rfl : u = r₂ := hι (by rw [hu', hr, div_eq_inv_mul, Units.val_inv_eq_inv_val])
  refine ⟨s, _, (hu.map (Scheme.stalkClosedPointTo y).hom).ne_zero, b₂, ?_, hb'⟩
  rw [Units.val_mul, mul_comm, ← hr, Base.valAt_stalk]

/- English proof (translation)
Rewrite using `[h0, h1, h2, ← mul_add, h3, mul_add]`.
-/
private theorem pullback_fin_relation {A A' B d lr lb S S' : ℝ} (h0 : A = A') (h1 : A' = d * lr) (h2 : B = d * lb)
    (h3 : lr + S = lb + S') : A + d * S = B + d * S' := by
  rw [h0, h1, h2, ← mul_add, h3, mul_add]

end SlopeTestRemainingChoices

/- English proof (translation)
The claim follows from `dif_pos hp.out`.
-/
private theorem lg_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) (w : Pad.Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) [hp : Fact (resP v).Prime] (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y.Y) :
  lgOf Y w v ε y = Real.log (ε.w (valAt y.1 (((∏ x : Pad.Letter Dw, (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose x.1 x.2 ^ expo Dw w x) *
        (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
          (fun τ i => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫ (Y.gr_spec (below y.1)).choose_spec.choose.v τ i) (resP v) (a.1 (resP v)) a.2.2 := dif_pos hp.out

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y w v hp ε y φ x g a hw hn hco`. Establish `: Algebra.IsAlgebraic ℚ (AlgebraicClosure F)` using `Algebra.IsAlgebraic.trans ℚ F _`. Take `⟨s, r, hr, b₂, e2, rfl⟩` from `coord_at Y hco _ (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose_spec.1 (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose_spec.2`. Establish `hlog` using `log_w_eq (resP v) ε _ (ioOf_le_one_iff _ (residueCharacteristic_mem v) ε)`. Establish `key` using `core _ g b₂ (ioOf (resP v) ε) (resP v) w hw hn hr`.

Conclude with `(lg_eq Y w v ε y).trans (pullback_fin_relation (congrArg (fun a => Real.log (ε.w a)) e2) (hlog _) (hlog _) key)`.
-/
theorem _root_.GlobalTheory.T.flag_point_local_height_prime : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) [Fact (resP v).Prime] (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y.Y) {φ : c.F →+* AlgebraicClosure F} {x : Sp (AlgebraicClosure F) ⟶ Z.X} (g : EigFrame Z φ x) (a : AlgebraicClosure F), (∀ s ∈ w.support, s.1 (resP v) = false) → (∀ s ∈ w.support, stepNorm Z.t (spMap (ioOf (resP v) ε) ≫ x) (fun τ i => spMap (dualMap (ioOf (resP v) ε)) ≫ g.v τ i) s.2.2 ≠ 0) → IsCoord Y y.1 g (expo Dw w) (((eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) a → lgOf Y w v ε y = Real.log (ε.w a) + (-Real.log (ε.w (resP v)) / Real.log (resP v)) * w.sum fun s n => (n : ℝ) * Real.log (stepNorm Z.t (spMap (ioOf (resP v) ε) ≫ x) (fun τ i => spMap (dualMap (ioOf (resP v) ε)) ≫ g.v τ i) s.2.2) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y w v hp ε y φ x g a hw hn hco
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure F) := Algebra.IsAlgebraic.trans ℚ F _
  obtain ⟨s, r, hr, b₂, e2, rfl⟩ := coord_at Y hco _
    (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose_spec.1
    (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose_spec.2
  have hlog := log_w_eq (resP v) ε _ (ioOf_le_one_iff _ (residueCharacteristic_mem v) ε)
  have key := core _ g b₂ (ioOf (resP v) ε) (resP v) w hw hn hr
  exact (lg_eq Y w v ε y).trans (pullback_fin_relation (congrArg (fun a => Real.log (ε.w a)) e2) (hlog _) (hlog _) key)
