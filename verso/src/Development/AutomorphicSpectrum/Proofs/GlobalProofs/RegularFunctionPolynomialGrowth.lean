import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactSpacePts
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffineOpenAndIsPushout
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

open CategoryTheory.Limits ReciprocityTheory.ChartRestriction.G.DVR.FlatBC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Gaga

/- English proof (translation)
Use `letI : Algebra R A := f.hom.toAlgebra`. Use `letI : Algebra R B := g.hom.toAlgebra`. Use `letI : Algebra A C := i.hom.toAlgebra`. Use `letI : Algebra B C := j.hom.toAlgebra`. Use `letI : Algebra R C := (f ≫ i).hom.toAlgebra`.

Use `haveI : IsScalarTower R A C := .of_algebraMap_eq fun r => rfl`. Use `haveI : IsScalarTower R B C := .of_algebraMap_eq fun r => congr($(h.w) r)`. Use `haveI : Algebra.IsPushout R B A C := CommRingCat.isPushout_iff_isPushout.mp h.flip`. Take `⟨t, rfl⟩` from `(Algebra.IsPushout.equiv R B A C).surjective c`. Proceed by induction on `t with`.

Consider the case `zero => simp`. Consider the case `tmul b a`. Rewrite using `[Algebra.IsPushout.equiv_tmul]`. Conclude with `AddSubmonoid.subset_closure ⟨a, b, mul_comm _ _⟩`. Consider the case `add x y hx hy`.

Rewrite using `[map_add]`. Conclude with `add_mem hx hy`.
-/
theorem mem_closure_of_isPushout {R A B C : CommRingCat.{0}} {f : R ⟶ A} {g : R ⟶ B} {i : A ⟶ C}
    {j : B ⟶ C} (h : IsPushout f g i j) (c : C) :
    c ∈ AddSubmonoid.closure {x : C | ∃ (a : A) (b : B), x = i a * j b} := by
  letI : Algebra R A := f.hom.toAlgebra
  letI : Algebra R B := g.hom.toAlgebra
  letI : Algebra A C := i.hom.toAlgebra
  letI : Algebra B C := j.hom.toAlgebra
  letI : Algebra R C := (f ≫ i).hom.toAlgebra
  haveI : IsScalarTower R A C := .of_algebraMap_eq fun r => rfl
  haveI : IsScalarTower R B C := .of_algebraMap_eq fun r => congr($(h.w) r)
  haveI : Algebra.IsPushout R B A C := CommRingCat.isPushout_iff_isPushout.mp h.flip
  obtain ⟨t, rfl⟩ := (Algebra.IsPushout.equiv R B A C).surjective c
  induction t with
  | zero => simp
  | tmul b a =>
    rw [Algebra.IsPushout.equiv_tmul]
    exact AddSubmonoid.subset_closure ⟨a, b, mul_comm _ _⟩
  | add x y hx hy =>
    rw [map_add]
    exact add_mem hx hy

/- English proof (translation)
Substitute `hD` using the available equality. Rewrite using `[← Scheme.Hom.app_eq_appLE]`. Conclude with `d.app_surjective O hO`.
-/
theorem appLE_surjective {X Z : Scheme.{0}} (d : X ⟶ Z) [IsClosedImmersion d] {O : Z.Opens}
    (hO : IsAffineOpen O) {D : X.Opens} (hD : D = d ⁻¹ᵁ O) (e : D ≤ d ⁻¹ᵁ O) :
    Function.Surjective (d.appLE O D e) := by
  subst hD
  rw [← Scheme.Hom.app_eq_appLE]
  exact d.app_surjective O hO

/- English proof (translation)
Establish `H` using `IsPullback.of_hasPullback p p`. Take `⟨hO, po⟩` from `Conormal.isAffineOpen_and_isPushout H (U := ⊤) (T₀ := W) (W := V) (isAffineOpen_top _) hW hV le_top le_top`. Establish `d1 : pullback.diagonal p ≫ pullback.fst p p = 𝟙 Y` using `pullback.diagonal_fst p`. Establish `d2 : pullback.diagonal p ≫ pullback.snd p p = 𝟙 Y` using `pullback.diagonal_snd p`. Establish `hD : V ⊓ W = pullback.diagonal p ⁻¹ᵁ (pullback.fst p p ⁻¹ᵁ V ⊓ pullback.snd p p ⁻¹ᵁ W)`.

Rewrite using `[Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, d1, d2]`. Simplify using the standard rewrite rules. Take `⟨c, rfl⟩` from `appLE_surjective (pullback.diagonal p) hO hD hD.le g`. Establish `hc` using `mem_closure_of_isPushout po c`. Proceed by induction on `hc using AddSubmonoid.closure_induction with`.

Consider the case `zero => simp`. Consider the case `mem x hx`. Take `⟨a, b, rfl⟩` from `hx`. Rewrite using `[map_mul]`. Use `AddSubmonoid.subset_closure ⟨a, b, ?_⟩` and prove the remaining obligations.

Establish `e₁` using `Conormal.appLE_appLE d1 (U := V) (V := pullback.fst p p ⁻¹ᵁ V ⊓ pullback.snd p p ⁻¹ᵁ W) (W := V ⊓ W) inf_le_left hD.le (by simpa using inf_le_left) a`. Establish `e₂` using `Conormal.appLE_appLE d2 (U := W) (V := pullback.fst p p ⁻¹ᵁ V ⊓ pullback.snd p p ⁻¹ᵁ W) (W := V ⊓ W) inf_le_right hD.le (by simpa using inf_le_right) b`. Rewrite using `[e₁, e₂]`. Conclude with `congrArg₂ (· * ·) (Conormal.id_appLE _ a) (Conormal.id_appLE _ b)`. Consider the case `add x y _ _ hx hy`.

Rewrite using `[map_add]`. Conclude with `add_mem hx hy`.
-/
theorem mem_closure_inf {S Y : Scheme.{0}} [IsAffine S] (p : Y ⟶ S) [IsSeparated p] {V W : Y.Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (g : Γ(Y, V ⊓ W)) :
    g ∈ AddSubmonoid.closure {x : Γ(Y, V ⊓ W) | ∃ (a : Γ(Y, V)) (b : Γ(Y, W)),
      x = resG Y inf_le_left a * resG Y inf_le_right b} := by
  have H := IsPullback.of_hasPullback p p
  obtain ⟨hO, po⟩ := Conormal.isAffineOpen_and_isPushout H (U := ⊤) (T₀ := W) (W := V)
    (isAffineOpen_top _) hW hV le_top le_top
  have d1 : pullback.diagonal p ≫ pullback.fst p p = 𝟙 Y := pullback.diagonal_fst p
  have d2 : pullback.diagonal p ≫ pullback.snd p p = 𝟙 Y := pullback.diagonal_snd p
  have hD : V ⊓ W = pullback.diagonal p ⁻¹ᵁ (pullback.fst p p ⁻¹ᵁ V ⊓ pullback.snd p p ⁻¹ᵁ W) := by
    rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, d1, d2]
    simp
  obtain ⟨c, rfl⟩ := appLE_surjective (pullback.diagonal p) hO hD hD.le g
  have hc := mem_closure_of_isPushout po c
  induction hc using AddSubmonoid.closure_induction with
  | zero => simp
  | mem x hx =>
    obtain ⟨a, b, rfl⟩ := hx
    rw [map_mul]
    refine AddSubmonoid.subset_closure ⟨a, b, ?_⟩
    have e₁ := Conormal.appLE_appLE d1 (U := V) (V := pullback.fst p p ⁻¹ᵁ V ⊓ pullback.snd p p ⁻¹ᵁ W)
      (W := V ⊓ W) inf_le_left hD.le (by simpa using inf_le_left) a
    have e₂ := Conormal.appLE_appLE d2 (U := W) (V := pullback.fst p p ⁻¹ᵁ V ⊓ pullback.snd p p ⁻¹ᵁ W)
      (W := V ⊓ W) inf_le_right hD.le (by simpa using inf_le_right) b
    rw [e₁, e₂]
    exact congrArg₂ (· * ·) (Conormal.id_appLE _ a) (Conormal.id_appLE _ b)
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy

variable {Y : Scheme.{0}} {p : Y ⟶ Sp ℂ}

def GensBdd (V W : Y.Opens) {n : ℕ} (u : Fin n → Γ(Y, V))
    (F : CxPts p (RingHom.id ℂ) → ℂ) : Prop :=
  ∃ (r m : ℕ) (w : Fin r → Γ(Y, W)), ∀ y ∈ ptsIn p (RingHom.id ℂ) (V ⊓ W),
    ‖F y‖ ≤ (∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) *
      (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m

variable {V W : Y.Opens} {n : ℕ} {u : Fin n → Γ(Y, V)}

/- English proof (translation)
Take `⟨r₁, m₁, w₁, h₁⟩` from `hF`. Take `⟨r₂, m₂, w₂, h₂⟩` from `hG`. Use `⟨r₁ + r₂, max m₁ m₂, Fin.append w₁ w₂, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hB : (1 : ℝ) ≤ 1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖` using `le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)`. Rewrite using `[Fin.sum_univ_add]`.

Simplify using `only [Fin.append_left, Fin.append_right]`. Establish `s₁ : 0 ≤ ∑ k, ‖ev p (RingHom.id ℂ) W (w₁ k) y‖` using `Finset.sum_nonneg fun _ _ => norm_nonneg _`. Establish `s₂ : 0 ≤ ∑ k, ‖ev p (RingHom.id ℂ) W (w₂ k) y‖` using `Finset.sum_nonneg fun _ _ => norm_nonneg _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GensBdd.add {F G : CxPts p (RingHom.id ℂ) → ℂ} (hF : GensBdd V W u F)
    (hG : GensBdd V W u G) : GensBdd V W u fun y => F y + G y := by
  obtain ⟨r₁, m₁, w₁, h₁⟩ := hF
  obtain ⟨r₂, m₂, w₂, h₂⟩ := hG
  refine ⟨r₁ + r₂, max m₁ m₂, Fin.append w₁ w₂, fun y hy => ?_⟩
  have hB : (1 : ℝ) ≤ 1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖ :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have s₁ : 0 ≤ ∑ k, ‖ev p (RingHom.id ℂ) W (w₁ k) y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have s₂ : 0 ≤ ∑ k, ‖ev p (RingHom.id ℂ) W (w₂ k) y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc ‖F y + G y‖ ≤ ‖F y‖ + ‖G y‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (h₁ y hy) (h₂ y hy)
    _ ≤ (∑ k, ‖ev p (RingHom.id ℂ) W (w₁ k) y‖) *
            (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ max m₁ m₂ +
          (∑ k, ‖ev p (RingHom.id ℂ) W (w₂ k) y‖) *
            (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ max m₁ m₂ :=
        add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (le_max_left _ _)) s₁)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (le_max_right _ _)) s₂)
    _ = _ := by ring

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on generalizing b with`. Consider the case `C a`. Use `⟨1, 0, fun _ => algX p W a * b, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hy'` using `mem_ptsIn_inf.1 hy`. Simplify using `[ev_mul, ev_algX hy'.1, ev_algX hy'.2]`.

Consider the case `add f g hf hg`. Simplify `(hf b).add (hg b)` using `only [map_add, ev_add, add_mul]`. Consider the case `mul_X f l hf`. Take `⟨r, m, w, h⟩` from `hf b`. Use `⟨r, m + 1, w, fun y hy => ?_⟩` and prove the remaining obligations.

Establish `hB : ‖ev p (RingHom.id ℂ) V (u l) y‖ ≤ 1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖` using `(Finset.single_le_sum (f := fun l => ‖ev p (RingHom.id ℂ) V (u l) y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ l)).trans (le_add_of_nonneg_left zero_le_one)`. Establish `s : 0 ≤ (∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m` using `(norm_nonneg _).trans (h y hy)`. Establish `e : ev p (RingHom.id ℂ) V (MvPolynomial.eval₂Hom (algX p V) u (f * MvPolynomial.X l)) y * ev p (RingHom.id ℂ) W b y = (ev p (RingHom.id ℂ) V (MvPolynomial.eval₂Hom (algX p V) u f) y * ev p (RingHom.id ℂ) W b y) * ev p (RingHom.id ℂ) V (u l) y`. Rewrite using `[map_mul, MvPolynomial.eval₂Hom_X', ev_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `beta_reduce`. Rewrite using `[e, norm_mul, pow_succ, ← mul_assoc]`. Conclude with `mul_le_mul (h y hy) hB (norm_nonneg _) s`.
-/
theorem gensBdd_eval₂ (f : MvPolynomial (Fin n) ℂ) (b : Γ(Y, W)) :
    GensBdd V W u fun y => ev p (RingHom.id ℂ) V (MvPolynomial.eval₂Hom (algX p V) u f) y *
      ev p (RingHom.id ℂ) W b y := by
  induction f using MvPolynomial.induction_on generalizing b with
  | C a =>
    refine ⟨1, 0, fun _ => algX p W a * b, fun y hy => ?_⟩
    have hy' := mem_ptsIn_inf.1 hy
    simp [ev_mul, ev_algX hy'.1, ev_algX hy'.2]
  | add f g hf hg =>
    simpa only [map_add, ev_add, add_mul] using (hf b).add (hg b)
  | mul_X f l hf =>
    obtain ⟨r, m, w, h⟩ := hf b
    refine ⟨r, m + 1, w, fun y hy => ?_⟩
    have hB : ‖ev p (RingHom.id ℂ) V (u l) y‖ ≤ 1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖ :=
      (Finset.single_le_sum (f := fun l => ‖ev p (RingHom.id ℂ) V (u l) y‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ l)).trans (le_add_of_nonneg_left zero_le_one)
    have s : 0 ≤ (∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) *
        (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m :=
      (norm_nonneg _).trans (h y hy)
    have e : ev p (RingHom.id ℂ) V (MvPolynomial.eval₂Hom (algX p V) u (f * MvPolynomial.X l)) y *
        ev p (RingHom.id ℂ) W b y =
        (ev p (RingHom.id ℂ) V (MvPolynomial.eval₂Hom (algX p V) u f) y *
          ev p (RingHom.id ℂ) W b y) * ev p (RingHom.id ℂ) V (u l) y := by
      rw [map_mul, MvPolynomial.eval₂Hom_X', ev_mul]
      ring
    beta_reduce
    rw [e, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (h y hy) hB (norm_nonneg _) s

/- English proof (translation)
Introduce `Y p hs hl V hV`. Establish `hc : (algX p V).FiniteType` using `(HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _).comp (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)`. Use `letI : Algebra ℂ Γ(Y, V) := (algX p V).toAlgebra`. Use `haveI : Algebra.FiniteType ℂ Γ(Y, V) := hc`. Take `⟨n, φ, hφ⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType ℂ Γ(Y, V))`.

Establish `hφe (f : MvPolynomial (Fin n) ℂ) : φ f = MvPolynomial.eval₂Hom (algX p V) (fun l => φ (MvPolynomial.X l)) f` using `by conv_lhs => rw [MvPolynomial.aeval_unique φ]`. Both sides reduce to the same expression. Use `⟨n, fun l => φ (MvPolynomial.X l), fun W hW g => ?_⟩` and prove the remaining obligations. Establish `key : GensBdd V W (p` using `p) (fun l => φ (MvPolynomial.X l)) (ev p (RingHom.id ℂ) (V ⊓ W) g) := by`. Proceed by induction on `mem_closure_inf p hV hW g using AddSubmonoid.closure_induction with`.

Consider the case `zero`. Use `⟨0, 0, Fin.elim0, fun y hy => ?_⟩` and prove the remaining obligations. Simplify using `[ev_eq hy]`. Consider the case `mem x hx`. Take `⟨a, b, rfl⟩` from `hx`.

Take `⟨f, rfl⟩` from `hφ a`. Take `⟨r, m, w, h⟩` from `gensBdd_eval₂ (V := V) (W := W) (p := p) (u := fun l => φ (MvPolynomial.X l)) f b`. Use `⟨r, m, w, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hy'` using `mem_ptsIn_inf.1 hy`. Rewrite using `[ev_mul, ev_res _ hy, ev_res _ hy, hφe]`.

Conclude with `h y hy`. Consider the case `add x y _ _ hx hy`. Establish `e : ev p (RingHom.id ℂ) (V ⊓ W) (x + y) = fun z => ev p (RingHom.id ℂ) (V ⊓ W) x z + ev p (RingHom.id ℂ) (V ⊓ W) y z`. Use function extensionality and compare the values at `fun z => ev_add x y z`. Rewrite using `[e]`.

Conclude with `hx.add hy`. Conclude with `key`.
-/
theorem exists_gens_bound : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsSeparated p → LocallyOfFiniteType p → ∀ (V : Y.Opens), IsAffineOpen V → ∃ (n : ℕ) (u : Fin n → Γ(Y, V)), ∀ (W : Y.Opens), IsAffineOpen W → ∀ g : Γ(Y, V ⊓ W), ∃ (r m : ℕ) (w : Fin r → Γ(Y, W)), ∀ y ∈ ptsIn p (RingHom.id ℂ) (V ⊓ W), ‖ev p (RingHom.id ℂ) (V ⊓ W) g y‖ ≤ (∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by
  intro Y p hs hl V hV
  have hc : (algX p V).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  letI : Algebra ℂ Γ(Y, V) := (algX p V).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(Y, V) := hc
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType ℂ Γ(Y, V))
  have hφe (f : MvPolynomial (Fin n) ℂ) :
      φ f = MvPolynomial.eval₂Hom (algX p V) (fun l => φ (MvPolynomial.X l)) f := by
    conv_lhs => rw [MvPolynomial.aeval_unique φ]
    rfl
  refine ⟨n, fun l => φ (MvPolynomial.X l), fun W hW g => ?_⟩
  have key : GensBdd V W (p := p) (fun l => φ (MvPolynomial.X l))
      (ev p (RingHom.id ℂ) (V ⊓ W) g) := by
    induction mem_closure_inf p hV hW g using AddSubmonoid.closure_induction with
    | zero =>
      refine ⟨0, 0, Fin.elim0, fun y hy => ?_⟩
      simp [ev_eq hy]
    | mem x hx =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨f, rfl⟩ := hφ a
      obtain ⟨r, m, w, h⟩ := gensBdd_eval₂ (V := V) (W := W) (p := p)
        (u := fun l => φ (MvPolynomial.X l)) f b
      refine ⟨r, m, w, fun y hy => ?_⟩
      have hy' := mem_ptsIn_inf.1 hy
      rw [ev_mul, ev_res _ hy, ev_res _ hy, hφe]
      exact h y hy
    | add x y _ _ hx hy =>
      have e : ev p (RingHom.id ℂ) (V ⊓ W) (x + y) =
          fun z => ev p (RingHom.id ℂ) (V ⊓ W) x z + ev p (RingHom.id ℂ) (V ⊓ W) y z :=
        funext fun z => ev_add x y z
      rw [e]
      exact hx.add hy
  exact key

end GlobalTheory.CompanionTheory.Gaga
