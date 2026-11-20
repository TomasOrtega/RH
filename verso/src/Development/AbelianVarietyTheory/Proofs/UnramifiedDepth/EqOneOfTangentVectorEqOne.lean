import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

section Alg

open Polynomial

variable {Ω : Type} [Field Ω] {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Rewrite using `[← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]`.
-/
theorem root_pow_eq_zero : AdjoinRoot.root ((X : Polynomial Ω) ^ p) ^ p = 0 := by
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]

def truncLift {A : Type} [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) :
    AdjoinRoot ((X : Polynomial Ω) ^ p) →ₐ[Ω] A :=
  Ideal.Quotient.liftₐ _ (aeval a) (by
    intro f hf
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton.1 hf
    simp [ha])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem truncLift_mk {A : Type} [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) (f : Polynomial Ω) :
    truncLift a ha (AdjoinRoot.mk _ f) = aeval a f := rfl

/- English proof (translation)
Rewrite using `[← AdjoinRoot.mk_X, truncLift_mk, aeval_X]`.
-/
theorem truncLift_root {A : Type} [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) :
    truncLift (Ω := Ω) a ha (AdjoinRoot.root _) = a := by
  rw [← AdjoinRoot.mk_X, truncLift_mk, aeval_X]

/- English proof (translation)
Establish `hp : p ≠ 0` using `(Fact.out : p.Prime).ne_zero`. Use `haveI : Nontrivial (AdjoinRoot ((X : Polynomial Ω) ^ p)) := (truncLift (0 : Ω) (zero_pow hp)).toRingHom.domain_nontrivial`. Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_` and prove the remaining obligations. Take `⟨f, rfl⟩` from `AdjoinRoot.mk_surjective a`. Establish `hn : IsNilpotent (AdjoinRoot.mk ((X : Polynomial Ω) ^ p) (X * f.divX))`.

Use `⟨p, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, mul_pow, AdjoinRoot.mk_X, root_pow_eq_zero, zero_mul]`. Rewrite using `[← X_mul_divX_add f, map_add]`. Distinguish the cases in `hc : f.coeff 0 = 0`. Use `right`.

Rewrite using `[hc, C_0, map_zero, add_zero]`. Conclude with `hn.isUnit_one_sub`. Use `left`. Conclude with `hn.isUnit_add_right_of_commute ((isUnit_C.2 (Ne.isUnit hc)).map _) (Commute.all _ _)`.
-/
theorem isLocalRing_trunc : IsLocalRing (AdjoinRoot ((X : Polynomial Ω) ^ p)) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : Nontrivial (AdjoinRoot ((X : Polynomial Ω) ^ p)) :=
    (truncLift (0 : Ω) (zero_pow hp)).toRingHom.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective a
  have hn : IsNilpotent (AdjoinRoot.mk ((X : Polynomial Ω) ^ p) (X * f.divX)) := by
    refine ⟨p, ?_⟩
    rw [map_mul, mul_pow, AdjoinRoot.mk_X, root_pow_eq_zero, zero_mul]
  rw [← X_mul_divX_add f, map_add]
  by_cases hc : f.coeff 0 = 0
  · right
    rw [hc, C_0, map_zero, add_zero]
    exact hn.isUnit_one_sub
  · left
    exact hn.isUnit_add_right_of_commute ((isUnit_C.2 (Ne.isUnit hc)).map _) (Commute.all _ _)

/- English proof (translation)
Rewrite `h` using `[AdjoinRoot.mk_eq_zero, X_pow_dvd_iff]`. Express the relevant statement in the definitionally equal form `_ = AdjoinRoot.mk _ (C _)`. Rewrite using `[AdjoinRoot.mk_eq_mk, X_pow_dvd_iff]`. Introduce `d hd`. Break down `d with _ | d` into its components or cases.

Simplify using `[coeff_zero_eq_eval_zero]`. Establish `h1` using `h d (by omega)`. Rewrite `h1` using `[coeff_derivative]`. Establish `h2 : ((d : Ω) + 1) ≠ 0`. Introduce `h0`.

Establish `: ((d + 1 : ℕ) : Ω) = 0` using `by exact_mod_cast h0`. Conclude with `absurd (Nat.le_of_dvd (Nat.succ_pos d) ((CharP.cast_eq_zero_iff Ω p _).1 this)) (by omega)`. Simplify `(mul_eq_zero.1 h1).resolve_right h2` using `[coeff_C]`.
-/
theorem mk_eq_const_of_derivative [CharP Ω p] (f : Polynomial Ω)
    (h : AdjoinRoot.mk ((X : Polynomial Ω) ^ p) (derivative f) = 0) :
    AdjoinRoot.mk ((X : Polynomial Ω) ^ p) f = algebraMap Ω _ (aeval (0 : Ω) f) := by
  rw [AdjoinRoot.mk_eq_zero, X_pow_dvd_iff] at h
  change _ = AdjoinRoot.mk _ (C _)
  rw [AdjoinRoot.mk_eq_mk, X_pow_dvd_iff]
  intro d hd
  rcases d with _ | d
  · simp [coeff_zero_eq_eval_zero]
  · have h1 := h d (by omega)
    rw [coeff_derivative] at h1
    have h2 : ((d : Ω) + 1) ≠ 0 := by
      intro h0
      have : ((d + 1 : ℕ) : Ω) = 0 := by exact_mod_cast h0
      exact absurd (Nat.le_of_dvd (Nat.succ_pos d) ((CharP.cast_eq_zero_iff Ω p _).1 this)) (by omega)
    simpa [coeff_C] using (mul_eq_zero.1 h1).resolve_right h2

end Alg

/- English proof (translation)
Take `⟨V, hV, hz, -⟩` from `exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y (IsLocalRing.closedPoint R)) trivial`. Establish `hr : Set.range y ⊆ Set.range hV.fromSpec`. Rewrite using `[hV.range_fromSpec]`. Introduce and unpack `_ ⟨x, rfl⟩`. Establish `: y ⁻¹ᵁ V = ⊤` using `(IsLocalRing.closed_point_mem_iff).mp hz`.

Conclude with `(this.ge (Set.mem_univ x) : x ∈ y ⁻¹ᵁ V)`. Take `⟨φ, rfl⟩ : ∃ φ : Γ(Y, V) ⟶ CommRingCat.of R, Spec.map φ ≫ hV.fromSpec = y` from `⟨Spec.preimage (IsOpenImmersion.lift hV.fromSpec y hr), by rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩`. Rewrite `h` using `[← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp]`. Establish `h'` using `Spec.map_injective h`. Rewrite using `[← Category.assoc, ← Spec.map_comp]`.

Use `congr 2`. Use extensionality with `a`. Conclude with `he _ (congrArg (fun k => k.hom a) h')`.
-/
theorem spMap_comp_eq_of_equalizer {R B : Type} [CommRing R] [CommRing B] [IsLocalRing R] {Y : Scheme.{0}}
    (y : Sp R ⟶ Y) (d₁ d₀ : R →+* B) (e : R →+* R) (he : ∀ x, d₁ x = d₀ x → e x = x)
    (h : spMap d₁ ≫ y = spMap d₀ ≫ y) : spMap e ≫ y = y := by
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := y (IsLocalRing.closedPoint R)) trivial
  have hr : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have : y ⁻¹ᵁ V = ⊤ := (IsLocalRing.closed_point_mem_iff).mp hz
    exact (this.ge (Set.mem_univ x) : x ∈ y ⁻¹ᵁ V)
  obtain ⟨φ, rfl⟩ : ∃ φ : Γ(Y, V) ⟶ CommRingCat.of R, Spec.map φ ≫ hV.fromSpec = y :=
    ⟨Spec.preimage (IsOpenImmersion.lift hV.fromSpec y hr), by rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  exact he _ (congrArg (fun k => k.hom a) h')

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Set `R` to `AdjoinRoot ((Polynomial.X : Polynomial Ω) ^ p)`. Use `haveI : IsLocalRing R := isLocalRing_trunc`. Set `t : R` to `AdjoinRoot.root _`. Establish `ht : t ^ p = 0` using `root_pow_eq_zero`.

Establish `heps : ∀ (B : Type) [CommRing B], (DualNumber.eps : DualNumber B) ^ p = 0` using `fun B _ => pow_eq_zero_of_le hp.two_le (by rw [sq, DualNumber.eps_mul_eps])`. Use `haveI : CharP R p := charP_of_injective_algebraMap (algebraMap Ω R).injective p`. Use `haveI : CharP (DualNumber R) p := charP_of_injective_algebraMap (algebraMap Ω (DualNumber R)).injective p`. Set `t' : DualNumber R` to `TrivSqZeroExt.inl t`. Establish `ht' : t' ^ p = 0`.

Express the relevant statement in the definitionally equal form `TrivSqZeroExt.inlAlgHom Ω R R t ^ p = 0`. Rewrite using `[← map_pow, ht, map_zero]`. Establish `hs : (t' + DualNumber.eps) ^ p = 0` using `by rw [add_pow_char, ht', heps, add_zero]`. Establish `he : g (DualNumber R) DualNumber.eps = 1`. Set `j : DualNumber Ω →ₐ[Ω] DualNumber R` to `DualNumber.lift ⟨(Algebra.ofId _ _, DualNumber.eps), DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩`.

Establish `hj : j DualNumber.eps = DualNumber.eps` using `DualNumber.lift_apply_eps _`. Rewrite using `[← hj, hg.1 _ _ j _ (heps Ω), h1, MonObj.comp_one]`. Establish `key : homAt s (truncLift _ hs) ≫ g R t = homAt s (truncLift _ ht') ≫ g R t`. Rewrite using `[← hg.1 _ _ _ _ ht, ← hg.1 _ _ _ _ ht, truncLift_root, truncLift_root, hg.2 _ _ _ ht' (heps R), he, _root_.mul_one]`. Set `e : R →ₐ[Ω] R` to `truncLift 0 (zero_pow hp.ne_zero)`.

Establish `hr : homAt s e ≫ g R t = g R t`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `spMap_comp_eq_of_equalizer (g R t).left (truncLift _ hs).toRingHom (truncLift _ ht').toRingHom e.toRingHom ?_ (congrArg (·.left) key)` and prove the remaining obligations. Introduce `x hx`. Take `⟨f, rfl⟩` from `AdjoinRoot.mk_surjective x`.

Express the relevant statement in the definitionally equal form `Polynomial.aeval (t' + DualNumber.eps) f = Polynomial.aeval t' f at hx`. Rewrite `hx` using `[Polynomial.aeval_add_of_sq_eq_zero _ _ _ (by rw [sq, DualNumber.eps_mul_eps]), add_eq_left]`. Establish `h3 : Polynomial.aeval t' (Polynomial.derivative f) = TrivSqZeroExt.inl (Polynomial.aeval t (Polynomial.derivative f))` using `Polynomial.aeval_algHom_apply (TrivSqZeroExt.inlAlgHom Ω R R) t _`. Establish `h4` using `congrArg TrivSqZeroExt.snd hx`. Rewrite `h4` using `[h3]`.

Establish `h5 : Polynomial.aeval t (Polynomial.derivative f) = 0` using `by simpa using h4`. Rewrite `h5` using `[AdjoinRoot.aeval_eq]`. Rewrite using `[mk_eq_const_of_derivative f h5]`. Conclude with `e.commutes _`. Establish `h0 : g R t = 1`.

Rewrite using `[← hr, ← hg.1 _ _ _ _ ht, truncLift_root, hg.zero hp.ne_zero]`. Use `hg.1 _ _ (truncLift a ha) t ht` as an intermediate fact. Rewrite `this` using `[truncLift_root, h0, MonObj.comp_one]`. Then use the resulting hypothesis.
-/
theorem IsAlpha.eq_one_of_tangent (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0})
    (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] (g : Fam s G) (hg : IsAlpha p s G g)
    (h1 : g (DualNumber Ω) DualNumber.eps = 1) (A : Type) [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) :
    g A a = 1 := by
  have hp : p.Prime := Fact.out
  let R := AdjoinRoot ((Polynomial.X : Polynomial Ω) ^ p)
  haveI : IsLocalRing R := isLocalRing_trunc
  let t : R := AdjoinRoot.root _
  have ht : t ^ p = 0 := root_pow_eq_zero
  have heps : ∀ (B : Type) [CommRing B], (DualNumber.eps : DualNumber B) ^ p = 0 := fun B _ =>
    pow_eq_zero_of_le hp.two_le (by rw [sq, DualNumber.eps_mul_eps])
  haveI : CharP R p := charP_of_injective_algebraMap (algebraMap Ω R).injective p
  haveI : CharP (DualNumber R) p := charP_of_injective_algebraMap (algebraMap Ω (DualNumber R)).injective p
  let t' : DualNumber R := TrivSqZeroExt.inl t
  have ht' : t' ^ p = 0 := by
    change TrivSqZeroExt.inlAlgHom Ω R R t ^ p = 0
    rw [← map_pow, ht, map_zero]
  have hs : (t' + DualNumber.eps) ^ p = 0 := by rw [add_pow_char, ht', heps, add_zero]
  have he : g (DualNumber R) DualNumber.eps = 1 := by
    let j : DualNumber Ω →ₐ[Ω] DualNumber R :=
      DualNumber.lift ⟨(Algebra.ofId _ _, DualNumber.eps), DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩
    have hj : j DualNumber.eps = DualNumber.eps := DualNumber.lift_apply_eps _
    rw [← hj, hg.1 _ _ j _ (heps Ω), h1, MonObj.comp_one]
  have key : homAt s (truncLift _ hs) ≫ g R t = homAt s (truncLift _ ht') ≫ g R t := by
    rw [← hg.1 _ _ _ _ ht, ← hg.1 _ _ _ _ ht, truncLift_root, truncLift_root, hg.2 _ _ _ ht' (heps R), he, _root_.mul_one]
  let e : R →ₐ[Ω] R := truncLift 0 (zero_pow hp.ne_zero)
  have hr : homAt s e ≫ g R t = g R t := by
    apply Over.OverMorphism.ext
    refine spMap_comp_eq_of_equalizer (g R t).left (truncLift _ hs).toRingHom (truncLift _ ht').toRingHom
      e.toRingHom ?_ (congrArg (·.left) key)
    intro x hx
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
    change Polynomial.aeval (t' + DualNumber.eps) f = Polynomial.aeval t' f at hx
    rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (by rw [sq, DualNumber.eps_mul_eps]), add_eq_left] at hx
    have h3 : Polynomial.aeval t' (Polynomial.derivative f) =
        TrivSqZeroExt.inl (Polynomial.aeval t (Polynomial.derivative f)) :=
      Polynomial.aeval_algHom_apply (TrivSqZeroExt.inlAlgHom Ω R R) t _
    have h4 := congrArg TrivSqZeroExt.snd hx
    rw [h3] at h4
    have h5 : Polynomial.aeval t (Polynomial.derivative f) = 0 := by simpa using h4
    rw [AdjoinRoot.aeval_eq] at h5
    rw [mk_eq_const_of_derivative f h5]
    exact e.commutes _
  have h0 : g R t = 1 := by
    rw [← hr, ← hg.1 _ _ _ _ ht, truncLift_root, hg.zero hp.ne_zero]
  have := hg.1 _ _ (truncLift a ha) t ht
  rwa [truncLift_root, h0, MonObj.comp_one] at this

end GlobalTheory.AlphaPair
end
