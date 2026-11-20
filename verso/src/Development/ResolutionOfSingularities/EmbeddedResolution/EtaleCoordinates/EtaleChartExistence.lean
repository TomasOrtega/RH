import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.Schemes.AffineOpens
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Apply `Quiver.Hom.unop_inj` to reduce the goal to its premises. Apply `Subsingleton.elim` to reduce the goal to its premises.
-/
private theorem opens_op_hom_ext {X : Scheme.{u}} {A B : (X.Opens)ᵒᵖ} (f g : A ⟶ B) : f = g := by
  apply Quiver.Hom.unop_inj
  apply Subsingleton.elim

/- English proof (translation)
Rewrite using `[opens_op_hom_ext f g]`.
-/
private theorem presheaf_map_eq {X : Scheme.{u}} {A B : (X.Opens)ᵒᵖ} (f g : A ⟶ B) :
    X.presheaf.map f = X.presheaf.map g := by
  rw [opens_op_hom_ext f g]

/- English proof (translation)
Simplify using the standard rewrite rules. Conclude with `(X.presheaf.map_comp _ _).symm.trans ((presheaf_map_eq _ _).trans (X.presheaf.map_comp _ _))`.
-/
private theorem appTop_homOfLE_comp_topIso_hom {X : Scheme.{u}} {V W : X.Opens} (h : W ≤ V) :
    Scheme.Hom.appTop (X.homOfLE h) ≫ W.topIso.hom =
      V.topIso.hom ≫ X.presheaf.map (homOfLE h).op := by
  simp
  exact (X.presheaf.map_comp _ _).symm.trans
    ((presheaf_map_eq _ _).trans (X.presheaf.map_comp _ _))

/- English proof (translation)
Establish `: IsAffine V.toScheme` using `hV`. Establish `hfac : V.toScheme.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p)) = V.ι ≫ p`. Rewrite using `[Scheme.isoSpec_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]`. Simplify using the standard rewrite rules. Establish `h3` using `congrArg (fun f : V.toScheme ⟶ Spec (CommRingCat.of k) => V.toScheme.isoSpec.inv ≫ f) hfac`.

Simplify using `only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h3`. Establish `h2 : AlgebraicGeometry.Smooth (Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p)))`. Rewrite using `[h3]`. Use `infer_instance`. Conclude with `AlgebraicGeometry.HasRingHomProperty.Spec_iff.mp h2`.
-/
private theorem smooth_ΓSpecIso_inv_comp_appTop {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (V : X.Opens)
    (hV : IsAffineOpen V) :
    RingHom.Smooth (CommRingCat.Hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p))) := by
  have : IsAffine V.toScheme := hV
  have hfac : V.toScheme.isoSpec.hom ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p)) =
        V.ι ≫ p := by
    rw [Scheme.isoSpec_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  have h3 := congrArg
    (fun f : V.toScheme ⟶ Spec (CommRingCat.of k) => V.toScheme.isoSpec.inv ≫ f) hfac
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h3
  have h2 : AlgebraicGeometry.Smooth
      (Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p))) := by
    rw [h3]
    infer_instance
  exact AlgebraicGeometry.HasRingHomProperty.Spec_iff.mp h2

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `: IsLocalRing (X.presheaf.stalk x)` using `inferInstance`. Establish `hnu : ∀ t ∈ s, t ∈ Ideal.comap (X.presheaf.germ U x hx).hom (IsLocalRing.maximalIdeal (X.presheaf.stalk x))`. Introduce `t ht`.

Rewrite using `[Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hunit`. Use `hcon t ht ((X.mem_basicOpen t x hx).mpr ?_)` and prove the remaining obligations. Conclude with `hunit`. Establish `hle` using `Ideal.span_le.mpr hnu`.

Rewrite `hle` using `[hs]`. Establish `h1` using `hle (Submodule.mem_top : (1 : Γ(X, U)) ∈ ⊤)`. Rewrite `h1` using `[Ideal.mem_comap, map_one]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top ((Ideal.eq_top_iff_one _).mpr h1)`.
-/
private theorem exists_mem_basicOpen_of_span_eq_top {X : Scheme.{u}} {U : X.Opens}
    (x : X) (hx : x ∈ U) (s : Set Γ(X, U)) (hs : Ideal.span s = ⊤) :
    ∃ t ∈ s, x ∈ X.basicOpen t := by
  by_contra hcon
  push Not at hcon
  have : IsLocalRing (X.presheaf.stalk x) := inferInstance
  have hnu : ∀ t ∈ s, t ∈ Ideal.comap (X.presheaf.germ U x hx).hom
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) := by
    intro t ht
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    refine hcon t ht ((X.mem_basicOpen t x hx).mpr ?_)
    exact hunit
  have hle := Ideal.span_le.mpr hnu
  rw [hs] at hle
  have h1 := hle (Submodule.mem_top : (1 : Γ(X, U)) ∈ ⊤)
  rw [Ideal.mem_comap, map_one] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top
    ((Ideal.eq_top_iff_one _).mpr h1)

/- English proof (translation)
Establish `: Fintype σ` using `Fintype.ofFinite σ`. Take `⟨n, ⟨g0⟩⟩` from `Finite.exists_equiv_fin ((Set.range P.map)ᶜ : Set ι)`. Take `⟨e, he⟩ : ∃ e : σ ⊕ ULift.{u} (Fin n) ≃ ι, ∀ s, e (Sum.inl s) = P.map s` from `⟨(Equiv.sumCongr (Equiv.ofInjective P.map P.map_inj) ((g0.trans (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n).symm).symm)).trans (Equiv.Set.sumCompl (Set.range P.map)), fun s => rfl⟩`. Use `⟨n, fun t => P.val (e (Sum.inr t)), ?_⟩` and prove the remaining obligations. Set `: Algebra (MvPolynomial (ULift.{u} (Fin n)) k) S` to `(MvPolynomial.eval₂Hom (algebraMap k S) fun t => P.val (e (Sum.inr t))).toAlgebra`.

Establish `halg : ∀ z : MvPolynomial (ULift.{u} (Fin n)) k, algebraMap (MvPolynomial (ULift.{u} (Fin n)) k) S z = MvPolynomial.eval₂Hom (algebraMap k S) (fun t => P.val (e (Sum.inr t))) z` using `fun _ => rfl`. Establish `: IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) S`. Use `IsScalarTower.of_algebraMap_eq fun a => ?_` and prove the remaining obligations. Rewrite using `[halg]`. Simplify using the standard rewrite rules.

Choose the witnesses or unpack the hypotheses as in `⟨Φ, hΦl, hΦr, hΦC⟩ : ∃ Φ : MvPolynomial ι k →+* MvPolynomial σ (MvPolynomial (ULift.{u} (Fin n)) k), (∀ s, Φ (MvPolynomial.X (e (Sum.inl s))) = MvPolynomial.X s) ∧ (∀ t, Φ (MvPolynomial.X (e (Sum.inr t))) = MvPolynomial.C (MvPolynomial.X t)) ∧ (∀ a : k, Φ (MvPolynomial.C a) = MvP …`. Use `⟨((MvPolynomial.aeval (fun i => Sum.elim (fun s => MvPolynomial.X s) (fun t => MvPolynomial.C (MvPolynomial.X t)) (e.symm i)) : MvPolynomial ι k →ₐ[k] MvPolynomial σ (MvPolynomial (ULift.{u} (Fin n)) k))).toRingHom, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s`. Simplify using the standard rewrite rules. Introduce `t`.

Simplify using the standard rewrite rules. Introduce `a`. Simplify using `[MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply k (MvPolynomial (ULift.{u} (Fin n)) k) (MvPolynomial σ (MvPolynomial (ULift.{u} (Fin n)) k))]`. Establish `hecases : ∀ i : ι, (∃ s, i = e (Sum.inl s)) ∨ (∃ t, i = e (Sum.inr t))`. Introduce `i`.

Break down `h : e.symm i with s | t` into its components or cases. Conclude with `Or.inl ⟨s, by rw [← h, e.apply_symm_apply]⟩`. Conclude with `Or.inr ⟨t, by rw [← h, e.apply_symm_apply]⟩`. Establish `hΦsurj : Function.Surjective Φ`. Introduce `z`.

Proceed by induction on `z using MvPolynomial.induction_on with`. Consider the case `C q`. Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨MvPolynomial.C a, hΦC a⟩`. Consider the case `add q₁ q₂ h₁ h₂`.

Take `⟨x, hx⟩` from `h₁`. Take `⟨y, hy⟩` from `h₂`. Conclude with `⟨x + y, by rw [map_add, hx, hy, ← map_add]⟩`. Consider the case `mul_X q t hq`. Take `⟨x, hx⟩` from `hq`.

Conclude with `⟨x * MvPolynomial.X (e (Sum.inr t)), by rw [map_mul, hx, hΦr, ← map_mul]⟩`. Consider the case `add z₁ z₂ h₁ h₂`. Take `⟨x, hx⟩` from `h₁`. Take `⟨y, hy⟩` from `h₂`. Conclude with `⟨x + y, by rw [map_add, hx, hy]⟩`.

Consider the case `mul_X z s hz`. Take `⟨x, hx⟩` from `hz`. Conclude with `⟨x * MvPolynomial.X (e (Sum.inl s)), by rw [map_mul, hx, hΦl]⟩`. Establish `hA : ∀ y : P.Ring, algebraMap P.Ring S y = MvPolynomial.aeval P.val y` using `fun y => Algebra.Generators.algebraMap_apply _ y`. Establish `hcompX : ∀ i : ι, (MvPolynomial.aeval (fun s => P.val (e (Sum.inl s)))) (Φ (MvPolynomial.X i)) = P.val i`.

Introduce `i`. Break down `hecases i with ⟨s, rfl⟩ | ⟨t, rfl⟩` into its components or cases. Rewrite using `[hΦl, MvPolynomial.aeval_X]`. Rewrite using `[hΦr, MvPolynomial.aeval_C, halg]`. Simplify using the standard rewrite rules.

Establish `hcomp : ∀ z : MvPolynomial ι k, (MvPolynomial.aeval (fun s => P.val (e (Sum.inl s)))) (Φ z) = MvPolynomial.aeval P.val z`. Introduce `z`. Proceed by induction on `z using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[hΦC, MvPolynomial.aeval_C, halg, MvPolynomial.aeval_C]`.

Simplify using the standard rewrite rules. Consider the case `add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]`. Consider the case `mul_X z i hz => simp only [map_mul, hz, hcompX, MvPolynomial.aeval_X]`. Establish `hpdX : ∀ (s : σ) (i : ι), MvPolynomial.pderiv s (Φ (MvPolynomial.X i)) = Φ (MvPolynomial.pderiv (P.map s) (MvPolynomial.X i))`. Introduce `s i`.

Break down `hecases i with ⟨s', rfl⟩ | ⟨t, rfl⟩` into its components or cases. Rewrite using `[hΦl, he]`. Distinguish the cases in `hss : s = s'`. Substitute `hss` using the available equality. Rewrite using `[MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_self, map_one]`.

Rewrite using `[MvPolynomial.pderiv_X_of_ne (Ne.symm hss), MvPolynomial.pderiv_X_of_ne (fun hh => hss (P.map_inj hh).symm), map_zero]`. Establish `hne : e (Sum.inr t) ≠ P.map s`. Introduce `hh`. Establish `hsum : (Sum.inr t : σ ⊕ ULift.{u} (Fin n)) = Sum.inl s`. Apply `e.injective` to reduce the goal to its premises.

Rewrite using `[hh, he]`. Simplify using `at hsum`. Rewrite using `[hΦr, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X_of_ne hne, map_zero]`. Establish `hpd : ∀ (s : σ) (q : MvPolynomial ι k), MvPolynomial.pderiv s (Φ q) = Φ (MvPolynomial.pderiv (P.map s) q)`. Introduce `s q`.

Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => rw [hΦC, MvPolynomial.pderiv_C, MvPolynomial.pderiv_C, map_zero]`. Consider the case `add q₁ q₂ h₁ h₂ => simp only [map_add, h₁, h₂]`. Consider the case `mul_X q i hq => simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hq, hpdX]`. Establish `hsurjW : Function.Surjective (MvPolynomial.aeval (R` using `MvPolynomial (ULift.{u} (Fin n)) k) (fun s => P.val (e (Sum.inl s)))) := by`.

Introduce `s`. Conclude with `⟨Φ (P.σ' s), by rw [hcomp, P.aeval_val_σ']⟩`. Set `G : Algebra.Generators (MvPolynomial (ULift.{u} (Fin n)) k) S σ` to `Algebra.Generators.ofSurjective (fun s => P.val (e (Sum.inl s))) hsurjW`. Establish `hGval : G.val = fun s => P.val (e (Sum.inl s))` using `rfl`. Establish `hspanQ : Ideal.span (Set.range fun j => Φ (P.relation j)) = G.ker`.

Establish `h1 : (Set.range fun j => Φ (P.relation j)) = ⇑Φ '' Set.range P.relation` using `Set.range_comp _ _`. Establish `h2 : P.ker = Ideal.comap Φ G.ker`. Rewrite using `[Algebra.Generators.ker_eq_ker_aeval_val, Algebra.Generators.ker_eq_ker_aeval_val]`. Use extensionality with `z`. Simplify using `only [Ideal.mem_comap, RingHom.mem_ker, hGval, hcomp]`.

Rewrite using `[h1, ← Ideal.map_span, P.span_range_relation_eq_ker, h2, Ideal.map_comap_of_surjective Φ hΦsurj]`. Take `⟨Q, hQmap, hQrel, hQalg⟩ : ∃ Q : Algebra.PreSubmersivePresentation (MvPolynomial (ULift.{u} (Fin n)) k) S σ σ, (∀ i, Q.map i = i) ∧ (∀ j, Q.relation j = Φ (P.relation j)) ∧ (∀ z, algebraMap Q.Ring S z = MvPolynomial.aeval (fun s => P.val (e (Sum.inl s))) z)` from `⟨{ toGenerators := G relation := fun j => Φ (P.relation j) span_range_relation_eq_ker := hspanQ map := id map_inj := Function.injective_id }, fun i => rfl, fun j => rfl, fun z => Algebra.Generators.algebraMap_apply G z⟩`. Establish `hmat : ∀ i j, Q.jacobiMatrix i j = Φ (P.jacobiMatrix i j)`. Introduce `i j`. Rewrite using `[Algebra.PreSubmersivePresentation.jacobiMatrix_apply, Algebra.PreSubmersivePresentation.jacobiMatrix_apply, hQmap, hQrel]`.

Conclude with `hpd i (P.relation j)`. Establish `hdet : Φ P.jacobiMatrix.det = Q.jacobiMatrix.det`. Rewrite using `[RingHom.map_det Φ P.jacobiMatrix, show Q.jacobiMatrix = P.jacobiMatrix.map ⇑Φ from Matrix.ext fun i j => hmat i j]`. Both sides reduce to the same expression. Establish `hjac : Q.jacobian = P.jacobian`.

Rewrite using `[Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hA, hQalg, ← hdet, hcomp]`. Establish `hunit : IsUnit Q.jacobian`. Rewrite using `[hjac]`. Conclude with `P.jacobian_isUnit`. Establish `: Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (ULift.{u} (Fin n)) k) S`.

Use `⟨σ, σ, inferInstance, inferInstance, ⟨Q, hunit⟩, ?_⟩` and prove the remaining obligations. Simplify using `[Algebra.Presentation.dimension]`. Use `show Algebra.Etale (MvPolynomial (ULift.{u} (Fin n)) k) S`. Use `infer_instance`.
-/
private theorem exists_etale_eval₂Hom_of_submersivePresentation {k S : Type u} [CommRing k] [CommRing S] [Algebra k S]
    {ι σ : Type} [Finite ι] [Finite σ] (P : Algebra.SubmersivePresentation k S ι σ) :
    ∃ (n : ℕ) (v : ULift.{u} (Fin n) → S),
      RingHom.Etale (MvPolynomial.eval₂Hom (algebraMap k S) v) := by
  classical
  have : Fintype σ := Fintype.ofFinite σ
  obtain ⟨n, ⟨g0⟩⟩ := Finite.exists_equiv_fin ((Set.range P.map)ᶜ : Set ι)
  obtain ⟨e, he⟩ : ∃ e : σ ⊕ ULift.{u} (Fin n) ≃ ι, ∀ s, e (Sum.inl s) = P.map s :=
    ⟨(Equiv.sumCongr (Equiv.ofInjective P.map P.map_inj)
        ((g0.trans (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n).symm).symm)).trans
          (Equiv.Set.sumCompl (Set.range P.map)), fun s => rfl⟩
  refine ⟨n, fun t => P.val (e (Sum.inr t)), ?_⟩
  let : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) S :=
    (MvPolynomial.eval₂Hom (algebraMap k S) fun t => P.val (e (Sum.inr t))).toAlgebra
  have halg : ∀ z : MvPolynomial (ULift.{u} (Fin n)) k,
      algebraMap (MvPolynomial (ULift.{u} (Fin n)) k) S z =
        MvPolynomial.eval₂Hom (algebraMap k S) (fun t => P.val (e (Sum.inr t))) z := fun _ => rfl
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) S := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [halg]
    simp
  obtain ⟨Φ, hΦl, hΦr, hΦC⟩ :
      ∃ Φ : MvPolynomial ι k →+* MvPolynomial σ (MvPolynomial (ULift.{u} (Fin n)) k),
        (∀ s, Φ (MvPolynomial.X (e (Sum.inl s))) = MvPolynomial.X s) ∧
        (∀ t, Φ (MvPolynomial.X (e (Sum.inr t))) = MvPolynomial.C (MvPolynomial.X t)) ∧
        (∀ a : k, Φ (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a)) := by
    refine ⟨((MvPolynomial.aeval (fun i => Sum.elim (fun s => MvPolynomial.X s)
        (fun t => MvPolynomial.C (MvPolynomial.X t)) (e.symm i)) :
          MvPolynomial ι k →ₐ[k] MvPolynomial σ (MvPolynomial (ULift.{u} (Fin n)) k))).toRingHom,
      ?_, ?_, ?_⟩
    · intro s; simp
    · intro t; simp
    · intro a
      simp [MvPolynomial.algebraMap_eq,
        IsScalarTower.algebraMap_apply k (MvPolynomial (ULift.{u} (Fin n)) k)
          (MvPolynomial σ (MvPolynomial (ULift.{u} (Fin n)) k))]
  have hecases : ∀ i : ι, (∃ s, i = e (Sum.inl s)) ∨ (∃ t, i = e (Sum.inr t)) := by
    intro i
    rcases h : e.symm i with s | t
    · exact Or.inl ⟨s, by rw [← h, e.apply_symm_apply]⟩
    · exact Or.inr ⟨t, by rw [← h, e.apply_symm_apply]⟩
  have hΦsurj : Function.Surjective Φ := by
    intro z
    induction z using MvPolynomial.induction_on with
    | C q =>
        induction q using MvPolynomial.induction_on with
        | C a => exact ⟨MvPolynomial.C a, hΦC a⟩
        | add q₁ q₂ h₁ h₂ =>
            obtain ⟨x, hx⟩ := h₁
            obtain ⟨y, hy⟩ := h₂
            exact ⟨x + y, by rw [map_add, hx, hy, ← map_add]⟩
        | mul_X q t hq =>
            obtain ⟨x, hx⟩ := hq
            exact ⟨x * MvPolynomial.X (e (Sum.inr t)), by rw [map_mul, hx, hΦr, ← map_mul]⟩
    | add z₁ z₂ h₁ h₂ =>
        obtain ⟨x, hx⟩ := h₁
        obtain ⟨y, hy⟩ := h₂
        exact ⟨x + y, by rw [map_add, hx, hy]⟩
    | mul_X z s hz =>
        obtain ⟨x, hx⟩ := hz
        exact ⟨x * MvPolynomial.X (e (Sum.inl s)), by rw [map_mul, hx, hΦl]⟩
  have hA : ∀ y : P.Ring, algebraMap P.Ring S y = MvPolynomial.aeval P.val y :=
    fun y => Algebra.Generators.algebraMap_apply _ y
  have hcompX : ∀ i : ι,
      (MvPolynomial.aeval (fun s => P.val (e (Sum.inl s)))) (Φ (MvPolynomial.X i)) = P.val i := by
    intro i
    rcases hecases i with ⟨s, rfl⟩ | ⟨t, rfl⟩
    · rw [hΦl, MvPolynomial.aeval_X]
    · rw [hΦr, MvPolynomial.aeval_C, halg]
      simp
  have hcomp : ∀ z : MvPolynomial ι k,
      (MvPolynomial.aeval (fun s => P.val (e (Sum.inl s)))) (Φ z) =
        MvPolynomial.aeval P.val z := by
    intro z
    induction z using MvPolynomial.induction_on with
    | C a =>
        rw [hΦC, MvPolynomial.aeval_C, halg, MvPolynomial.aeval_C]
        simp
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | mul_X z i hz => simp only [map_mul, hz, hcompX, MvPolynomial.aeval_X]
  have hpdX : ∀ (s : σ) (i : ι),
      MvPolynomial.pderiv s (Φ (MvPolynomial.X i)) =
        Φ (MvPolynomial.pderiv (P.map s) (MvPolynomial.X i)) := by
    intro s i
    rcases hecases i with ⟨s', rfl⟩ | ⟨t, rfl⟩
    · rw [hΦl, he]
      by_cases hss : s = s'
      · subst hss
        rw [MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_self, map_one]
      · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hss),
          MvPolynomial.pderiv_X_of_ne (fun hh => hss (P.map_inj hh).symm), map_zero]
    · have hne : e (Sum.inr t) ≠ P.map s := by
        intro hh
        have hsum : (Sum.inr t : σ ⊕ ULift.{u} (Fin n)) = Sum.inl s := by
          apply e.injective
          rw [hh, he]
        simp at hsum
      rw [hΦr, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X_of_ne hne, map_zero]
  have hpd : ∀ (s : σ) (q : MvPolynomial ι k),
      MvPolynomial.pderiv s (Φ q) = Φ (MvPolynomial.pderiv (P.map s) q) := by
    intro s q
    induction q using MvPolynomial.induction_on with
    | C a => rw [hΦC, MvPolynomial.pderiv_C, MvPolynomial.pderiv_C, map_zero]
    | add q₁ q₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | mul_X q i hq => simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hq, hpdX]
  have hsurjW : Function.Surjective
      (MvPolynomial.aeval (R := MvPolynomial (ULift.{u} (Fin n)) k)
        (fun s => P.val (e (Sum.inl s)))) := by
    intro s
    exact ⟨Φ (P.σ' s), by rw [hcomp, P.aeval_val_σ']⟩
  let G : Algebra.Generators (MvPolynomial (ULift.{u} (Fin n)) k) S σ :=
    Algebra.Generators.ofSurjective (fun s => P.val (e (Sum.inl s))) hsurjW
  have hGval : G.val = fun s => P.val (e (Sum.inl s)) := rfl
  have hspanQ : Ideal.span (Set.range fun j => Φ (P.relation j)) = G.ker := by
    have h1 : (Set.range fun j => Φ (P.relation j)) = ⇑Φ '' Set.range P.relation :=
      Set.range_comp _ _
    have h2 : P.ker = Ideal.comap Φ G.ker := by
      rw [Algebra.Generators.ker_eq_ker_aeval_val, Algebra.Generators.ker_eq_ker_aeval_val]
      ext z
      simp only [Ideal.mem_comap, RingHom.mem_ker, hGval, hcomp]
    rw [h1, ← Ideal.map_span, P.span_range_relation_eq_ker, h2,
      Ideal.map_comap_of_surjective Φ hΦsurj]
  obtain ⟨Q, hQmap, hQrel, hQalg⟩ :
      ∃ Q : Algebra.PreSubmersivePresentation (MvPolynomial (ULift.{u} (Fin n)) k) S σ σ,
        (∀ i, Q.map i = i) ∧ (∀ j, Q.relation j = Φ (P.relation j)) ∧
        (∀ z, algebraMap Q.Ring S z =
          MvPolynomial.aeval (fun s => P.val (e (Sum.inl s))) z) :=
    ⟨{ toGenerators := G
       relation := fun j => Φ (P.relation j)
       span_range_relation_eq_ker := hspanQ
       map := id
       map_inj := Function.injective_id },
      fun i => rfl, fun j => rfl, fun z => Algebra.Generators.algebraMap_apply G z⟩
  have hmat : ∀ i j, Q.jacobiMatrix i j = Φ (P.jacobiMatrix i j) := by
    intro i j
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
      Algebra.PreSubmersivePresentation.jacobiMatrix_apply, hQmap, hQrel]
    exact hpd i (P.relation j)
  have hdet : Φ P.jacobiMatrix.det = Q.jacobiMatrix.det := by
    rw [RingHom.map_det Φ P.jacobiMatrix,
      show Q.jacobiMatrix = P.jacobiMatrix.map ⇑Φ from Matrix.ext fun i j => hmat i j]
    rfl
  have hjac : Q.jacobian = P.jacobian := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hA, hQalg, ← hdet, hcomp]
  have hunit : IsUnit Q.jacobian := by
    rw [hjac]
    exact P.jacobian_isUnit
  have : Algebra.IsStandardSmoothOfRelativeDimension 0
      (MvPolynomial (ULift.{u} (Fin n)) k) S := by
    refine ⟨σ, σ, inferInstance, inferInstance, ⟨Q, hunit⟩, ?_⟩
    simp [Algebra.Presentation.dimension]
  show Algebra.Etale (MvPolynomial (ULift.{u} (Fin n)) k) S
  infer_instance

/- English proof (translation)
Rewrite using `[Category.assoc, c.comp_struct, ← Category.assoc, Scheme.homOfLE_ι]`.
-/
private theorem homOfLE_comp_map_comp_affineSpaceFinToSpec {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    {V : X.Opens} (hVU : V ≤ U) :
    (X.homOfLE hVU ≫ c.map) ≫ affineSpaceFinToSpec k m = V.ι ≫ p := by
  rw [Category.assoc, c.comp_struct, ← Category.assoc, Scheme.homOfLE_ι]

/- English proof (translation)
Use `c.isEtale` as an intermediate fact. Use `infer_instance`.
-/
private theorem etale_homOfLE_comp_map {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    {V : X.Opens} (hVU : V ≤ U) :
    AlgebraicGeometry.Etale (X.homOfLE hVU ≫ c.map) := by
  have := c.isEtale
  infer_instance

def EtaleChart.restrict {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    {V : X.Opens} (hVU : V ≤ U) : EtaleChart p V m where
  map := X.homOfLE hVU ≫ c.map
  comp_struct := homOfLE_comp_map_comp_affineSpaceFinToSpec c hVU
  isEtale := etale_homOfLE_comp_map c hVU

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem EtaleChart.restrict_map {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    {V : X.Opens} (hVU : V ≤ U) :
    (c.restrict hVU).map = X.homOfLE hVU ≫ c.map := rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem homOfVector_comp_affineSpaceFinToSpec {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) {m : ℕ}
    (v : ULift.{u} (Fin m) → U.toScheme.presheaf.obj (op ⊤)) :
    AffineSpace.homOfVector (U.ι ≫ p) v ≫ affineSpaceFinToSpec k m = U.ι ≫ p := by
  simp

def EtaleChart.ofCoords {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) {m : ℕ}
    (v : ULift.{u} (Fin m) → U.toScheme.presheaf.obj (op ⊤))
    (he : AlgebraicGeometry.Etale (AffineSpace.homOfVector (U.ι ≫ p) v)) :
    EtaleChart p U m where
  map := AffineSpace.homOfVector (U.ι ≫ p) v
  comp_struct := homOfVector_comp_affineSpaceFinToSpec p U v
  isEtale := he

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem EtaleChart.ofCoords_map {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) {m : ℕ}
    (v : ULift.{u} (Fin m) → U.toScheme.presheaf.obj (op ⊤))
    (he : AlgebraicGeometry.Etale (AffineSpace.homOfVector (U.ι ≫ p) v)) :
    (EtaleChart.ofCoords p U v he).map = AffineSpace.homOfVector (U.ι ≫ p) v := rfl

/- English proof (translation)
Take `⟨V, hxV, hV⟩` from `Scheme.exists_isAffineOpen_mem (X := X) x`. Establish `: IsAffine V.toScheme` using `hV`. Use `set θV : CommRingCat.of k ⟶ Γ(V.toScheme, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p) with hθVdef`. Use `set ψV : CommRingCat.of k ⟶ Γ(X, V) := θV ≫ V.topIso.hom with hψVdef`. Establish `hsmV : RingHom.Smooth ψV.hom`.

Establish `h1 : RingHom.Smooth θV.hom` using `smooth_ΓSpecIso_inv_comp_appTop p V hV`. Establish `h2` using `RingHom.Smooth.respectsIso.left θV.hom V.topIso.commRingCatIsoToRingEquiv h1`. Rewrite using `[hψVdef, CommRingCat.hom_comp]`. Conclude with `h2`. Take `⟨s, hspan, hloc⟩` from `RingHom.Smooth.locally_isStandardSmooth hsmV`.

Take `⟨t, hts, hxt⟩` from `exists_mem_basicOpen_of_span_eq_top x hxV s hspan`. Establish `hUV : X.basicOpen t ≤ V` using `X.basicOpen_le t`. Establish `hU : IsAffineOpen (X.basicOpen t)` using `hV.basicOpen t`. Establish `: IsAffine (X.basicOpen t).toScheme` using `hU`. Use `set θU : CommRingCat.of k ⟶ Γ((X.basicOpen t).toScheme, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop ((X.basicOpen t).ι ≫ p) with hθUdef`.

Use `set ψU : CommRingCat.of k ⟶ Γ(X, X.basicOpen t) := θU ≫ (X.basicOpen t).topIso.hom with hψUdef`. Establish `hψUeq : ψU = ψV ≫ X.presheaf.map (homOfLE hUV).op`. Establish `e1 : (X.basicOpen t).ι ≫ p = X.homOfLE hUV ≫ (V.ι ≫ p)`. Rewrite using `[← Category.assoc, Scheme.homOfLE_ι]`. Rewrite using `[hψUdef, hθUdef, e1, Scheme.Hom.comp_appTop, hψVdef, hθVdef]`.

Simplify using `only [Category.assoc]`. Rewrite using `[appTop_homOfLE_comp_topIso_hom]`. Establish `hstdψU : RingHom.IsStandardSmooth ψU.hom`. Use `hV.isLocalization_basicOpen t` as an intermediate fact. Establish `h1` using `RingHom.isStandardSmooth_respectsIso.left ((algebraMap Γ(X, V) (Localization.Away t)).comp ψV.hom) (IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t) Γ(X, X.basicOpen t)).toRingEquiv (hloc t hts)`.

Establish `h2 : (((IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t) Γ(X, X.basicOpen t)).toRingEquiv : Localization.Away t →+* Γ(X, X.basicOpen t)).comp ((algebraMap Γ(X, V) (Localization.Away t)).comp ψV.hom)) = ψU.hom`. Rewrite using `[hψUeq, CommRingCat.hom_comp]`. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`. Conclude with `(IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t) Γ(X, X.basicOpen t)).commutes (ψV.hom a)`.

Rewrite using `[← h2]`. Conclude with `h1`. Establish `hstdθU : RingHom.IsStandardSmooth θU.hom`. Establish `h1` using `RingHom.isStandardSmooth_respectsIso.left ψU.hom (X.basicOpen t).topIso.symm.commRingCatIsoToRingEquiv hstdψU`. Establish `h3 : θU = ψU ≫ (X.basicOpen t).topIso.inv`.

Rewrite using `[hψUdef, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Establish `h2 : (((X.basicOpen t).topIso.symm.commRingCatIsoToRingEquiv : Γ(X, X.basicOpen t) →+* Γ((X.basicOpen t).toScheme, ⊤)).comp ψU.hom) = θU.hom`. Rewrite using `[h3, CommRingCat.hom_comp]`. Both sides reduce to the same expression. Rewrite using `[← h2]`.

Conclude with `h1`. Set `: Algebra (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤)` to `θU.hom.toAlgebra`. Establish `hAlg : Algebra.IsStandardSmooth (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤)` using `hstdθU`. Take `⟨⟨ι, σ, hσ, hι, ⟨P⟩⟩⟩` from `hAlg`. Establish `: Finite σ` using `hσ`.

Establish `: Finite ι` using `hι`. Take `⟨n, v, hv⟩` from `exists_etale_eval₂Hom_of_submersivePresentation P`. Use `set φ : CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) (CommRingCat.of k)) ⟶ Γ((X.basicOpen t).toScheme, ⊤) := CommRingCat.ofHom (MvPolynomial.eval₂Hom (algebraMap (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤)) v) with hφdef`. Establish `: AlgebraicGeometry.Etale (Spec.map φ)` using `AlgebraicGeometry.HasRingHomProperty.Spec_iff.mpr hv`. Establish `hφC : CommRingCat.ofHom MvPolynomial.C ≫ φ = θU`.

Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`. Use `show MvPolynomial.eval₂ (algebraMap (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤)) v (MvPolynomial.C a) = θU.hom a`. Conclude with `MvPolynomial.eval₂_C _ _ a`.

Establish `hcs : ((X.basicOpen t).toScheme.isoSpec.hom ≫ Spec.map φ ≫ (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).inv) ≫ affineSpaceFinToSpec k n = (X.basicOpen t).ι ≫ p`. Rewrite using `[Category.assoc, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp, hφC, hθUdef]`. Rewrite using `[Scheme.isoSpec_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]`. Simplify using the standard rewrite rules. Conclude with `⟨X.basicOpen t, n, hxt, hU, ⟨⟨(X.basicOpen t).toScheme.isoSpec.hom ≫ Spec.map φ ≫ (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).inv, hcs, inferInstance⟩⟩⟩`.
-/
theorem exists_etaleChart {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    ∃ (U : X.Opens) (m : ℕ), x ∈ U ∧ IsAffineOpen U ∧ Nonempty (EtaleChart p U m) := by
  classical
  obtain ⟨V, hxV, hV⟩ := Scheme.exists_isAffineOpen_mem (X := X) x
  have : IsAffine V.toScheme := hV
  set θV : CommRingCat.of k ⟶ Γ(V.toScheme, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p) with hθVdef
  set ψV : CommRingCat.of k ⟶ Γ(X, V) := θV ≫ V.topIso.hom with hψVdef
  have hsmV : RingHom.Smooth ψV.hom := by
    have h1 : RingHom.Smooth θV.hom := smooth_ΓSpecIso_inv_comp_appTop p V hV
    have h2 := RingHom.Smooth.respectsIso.left θV.hom V.topIso.commRingCatIsoToRingEquiv h1
    rw [hψVdef, CommRingCat.hom_comp]
    exact h2
  obtain ⟨s, hspan, hloc⟩ := RingHom.Smooth.locally_isStandardSmooth hsmV
  obtain ⟨t, hts, hxt⟩ := exists_mem_basicOpen_of_span_eq_top x hxV s hspan
  have hUV : X.basicOpen t ≤ V := X.basicOpen_le t
  have hU : IsAffineOpen (X.basicOpen t) := hV.basicOpen t
  have : IsAffine (X.basicOpen t).toScheme := hU
  set θU : CommRingCat.of k ⟶ Γ((X.basicOpen t).toScheme, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      Scheme.Hom.appTop ((X.basicOpen t).ι ≫ p) with hθUdef
  set ψU : CommRingCat.of k ⟶ Γ(X, X.basicOpen t) :=
    θU ≫ (X.basicOpen t).topIso.hom with hψUdef
  have hψUeq : ψU = ψV ≫ X.presheaf.map (homOfLE hUV).op := by
    have e1 : (X.basicOpen t).ι ≫ p = X.homOfLE hUV ≫ (V.ι ≫ p) := by
      rw [← Category.assoc, Scheme.homOfLE_ι]
    rw [hψUdef, hθUdef, e1, Scheme.Hom.comp_appTop, hψVdef, hθVdef]
    simp only [Category.assoc]
    rw [appTop_homOfLE_comp_topIso_hom]
  have hstdψU : RingHom.IsStandardSmooth ψU.hom := by
    have := hV.isLocalization_basicOpen t
    have h1 := RingHom.isStandardSmooth_respectsIso.left
      ((algebraMap Γ(X, V) (Localization.Away t)).comp ψV.hom)
      (IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t)
        Γ(X, X.basicOpen t)).toRingEquiv (hloc t hts)
    have h2 : (((IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t)
        Γ(X, X.basicOpen t)).toRingEquiv : Localization.Away t →+* Γ(X, X.basicOpen t)).comp
        ((algebraMap Γ(X, V) (Localization.Away t)).comp ψV.hom)) = ψU.hom := by
      rw [hψUeq, CommRingCat.hom_comp]
      apply RingHom.ext
      intro a
      exact (IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t)
        Γ(X, X.basicOpen t)).commutes (ψV.hom a)
    rw [← h2]
    exact h1
  have hstdθU : RingHom.IsStandardSmooth θU.hom := by
    have h1 := RingHom.isStandardSmooth_respectsIso.left ψU.hom
      (X.basicOpen t).topIso.symm.commRingCatIsoToRingEquiv hstdψU
    have h3 : θU = ψU ≫ (X.basicOpen t).topIso.inv := by
      rw [hψUdef, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h2 : (((X.basicOpen t).topIso.symm.commRingCatIsoToRingEquiv :
        Γ(X, X.basicOpen t) →+* Γ((X.basicOpen t).toScheme, ⊤)).comp ψU.hom) = θU.hom := by
      rw [h3, CommRingCat.hom_comp]
      rfl
    rw [← h2]
    exact h1
  let : Algebra (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤) := θU.hom.toAlgebra
  have hAlg : Algebra.IsStandardSmooth (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤) :=
    hstdθU
  obtain ⟨⟨ι, σ, hσ, hι, ⟨P⟩⟩⟩ := hAlg
  have : Finite σ := hσ
  have : Finite ι := hι
  obtain ⟨n, v, hv⟩ := exists_etale_eval₂Hom_of_submersivePresentation P
  set φ : CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) (CommRingCat.of k)) ⟶
      Γ((X.basicOpen t).toScheme, ⊤) :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom
      (algebraMap (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤)) v) with hφdef
  have : AlgebraicGeometry.Etale (Spec.map φ) :=
    AlgebraicGeometry.HasRingHomProperty.Spec_iff.mpr hv
  have hφC : CommRingCat.ofHom MvPolynomial.C ≫ φ = θU := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    show MvPolynomial.eval₂
        (algebraMap (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤)) v (MvPolynomial.C a)
      = θU.hom a
    exact MvPolynomial.eval₂_C _ _ a
  have hcs : ((X.basicOpen t).toScheme.isoSpec.hom ≫ Spec.map φ ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).inv) ≫
        affineSpaceFinToSpec k n = (X.basicOpen t).ι ≫ p := by
    rw [Category.assoc, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp, hφC,
      hθUdef]
    rw [Scheme.isoSpec_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  exact ⟨X.basicOpen t, n, hxt, hU,
    ⟨⟨(X.basicOpen t).toScheme.isoSpec.hom ≫ Spec.map φ ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).inv, hcs, inferInstance⟩⟩⟩

/- English proof (translation)
Take `⟨U, m, hxU, hU, ⟨c⟩⟩` from `exists_etaleChart p x`. Establish `hxUW : x ∈ (U ⊓ W : X.Opens)` using `⟨hxU, hx⟩`. Take `⟨f, hfle, hxf⟩` from `hU.exists_basicOpen_le (⟨x, hxUW⟩ : (U ⊓ W : X.Opens)) hxU`. Establish `hle : X.basicOpen f ≤ U` using `X.basicOpen_le f`. Conclude with `⟨X.basicOpen f, m, hxf, le_trans hfle inf_le_right, hU.basicOpen f, ⟨c.restrict hle⟩⟩`.
-/
theorem exists_etaleChart_le {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X)
    (W : X.Opens) (hx : x ∈ W) :
    ∃ (U : X.Opens) (m : ℕ), x ∈ U ∧ U ≤ W ∧ IsAffineOpen U ∧ Nonempty (EtaleChart p U m) := by
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  have hxUW : x ∈ (U ⊓ W : X.Opens) := ⟨hxU, hx⟩
  obtain ⟨f, hfle, hxf⟩ := hU.exists_basicOpen_le (⟨x, hxUW⟩ : (U ⊓ W : X.Opens)) hxU
  have hle : X.basicOpen f ≤ U := X.basicOpen_le f
  exact ⟨X.basicOpen f, m, hxf, le_trans hfle inf_le_right, hU.basicOpen f, ⟨c.restrict hle⟩⟩

end FunctorialResolution.EmbeddedResolution
