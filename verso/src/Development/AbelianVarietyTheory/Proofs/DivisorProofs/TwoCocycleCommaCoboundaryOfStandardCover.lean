import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleInvertibleLocusIsCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsInvertibleLocusOfBasisFunctorStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc

open Classical in

/- English proof (translation)
Introduce `R _ C _ C' _ F G _ _ H hcov hfil T n d hd z hz hy`. Use `choose y hy using hy`. Establish `hu : ∀ {t t' : C'} {u : T ⟶ G.obj t} (a : t ⟶ t') {x : F.obj T}, IsUnit (mp F u x) → IsUnit (mp F (u ≫ G.map a) x)` using `fun a _ h ↦ isUnit_comp _ h`. Establish `h1` using `fun i j : Fin n ↦ GlobalTheory.T.oneCocycle_invertibleLocus_isCoboundary_alt F G H hcov hfil T (d i * d j) (fun t t' u a ↦ y j t t' u a - y i t t' u a) fun t t' t'' u a b h ↦ by`. Rewrite `h` using `[map_mul, IsUnit.mul_iff]`.

Rewrite using `[map_sub]`. Take the linear combination `hy i t t' t'' u a b h.1 - hy j t t' t'' u a b h.2`. Use `choose β hβ' using h1`. Establish `hβ : ∀ i j t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u (d i)) → IsUnit (mp F u (d j)) → β i j t' (u ≫ G.map a) - mp F (G.map a) (β i j t u) = y j t t' u a - y i t t' u a` using `fun i j t t' u a hi hj ↦ hβ' i j t t' u a (by rw [map_mul]; exact hi.mul hj)`. Establish `h2` using `fun i j k : Fin n ↦ GlobalTheory.T.sections_invertibleLocus_of_basisFunctor F G H hcov hfil T (d i * d j * d k) (fun t u ↦ β j k t u - β i k t u + β i j t u) fun t t' u a h ↦ by`.

Rewrite `h` using `[map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff]`. Rewrite using `[map_add, map_sub]`. Take the linear combination `hβ j k t t' u a h.1.2 h.2 - hβ i k t t' u a h.1.1 h.2 + hβ i j t t' u a h.1.1 h.1.2`. Use `choose x hx' hxs' using h2`. Establish `hx : ∀ i j k, IsSec F (fun S u ↦ (IsUnit (mp F u (d i)) ∧ IsUnit (mp F u (d j))) ∧ IsUnit (mp F u (d k))) (x i j k)` using `fun i j k S S' u ψ h ↦ hx' i j k S S' u ψ (by show IsUnit _`.

Rewrite using `[map_mul, map_mul]`. Conclude with `(h.1.1.mul h.1.2).mul h.2)`. Establish `hxs : ∀ i j k t (u : T ⟶ G.obj t), IsUnit (mp F u (d i)) → IsUnit (mp F u (d j)) → IsUnit (mp F u (d k)) → x i j k (G.obj t) u = β j k t u - β i k t u + β i j t u` using `fun i j k t u hi hj hk ↦ hxs' i j k t u (by rw [map_mul, map_mul]; exact (hi.mul hj).mul hk)`. Take `⟨e, he, he'⟩` from `cech2 H hd x hx (fun l i j k S u hl hi hj hk ↦ by`. Take `⟨m, b, hb, hb'⟩` from `hcov S`.

Use `sep_std H hb _ fun S' ψ ⟨r, hr⟩ ↦ ?_` and prove the remaining obligations. Take `⟨t, v, w, rfl⟩` from `hb' r S' ψ hr`. Establish `hl'` using `isUnit_comp v hl`. Establish `hi'` using `isUnit_comp v hi`. Establish `hj'` using `isUnit_comp v hj`.

Establish `hk'` using `isUnit_comp v hk`. Rewrite using `[mp_comp, map_sub (mp F v), map_add (mp F v), map_sub (mp F v), ← hx i j k S _ u v ⟨⟨hi, hj⟩, hk⟩, ← hx l j k S _ u v ⟨⟨hl, hj⟩, hk⟩, ← hx l i k S _ u v ⟨⟨hl, hi⟩, hk⟩, ← hx l i j S _ u v ⟨⟨hl, hi⟩, hj⟩, hxs _ _ _ _ _ hi' hj' hk', hxs _ _ _ _ _ hl' hj' hk', hxs _ _ _ _ _ hl' hi' …`. Put the polynomial expressions in normal form. Conclude with `map_zero _)`. Choose the witnesses or unpack the hypotheses as in `⟨γ, hγ⟩ : ∃ γ : Fin n → ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ i j t u, IsUnit (mp F u (d i)) → IsUnit (mp F u (d j)) → γ j t u - γ i t u = β i j t u - e i j (G.obj t) u := by`.

Use `⟨fun i t u ↦ if h : ∃ i, IsUnit (mp F u (d i)) then β h.choose i t u - e h.choose i _ u else 0, fun i j t u hi hj ↦ ?_⟩` and prove the remaining obligations. Establish `h : ∃ i, IsUnit (mp F u (d i))` using `⟨i, hi⟩`. Simplify using `only [dif_pos h]`. Take the linear combination `-he' _ i j _ u h.choose_spec hi hj + hxs _ i j t u h.choose_spec hi hj`. Choose the witnesses or unpack the hypotheses as in `⟨α, hα⟩ : ∃ α : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ i t t' u a, IsUnit (mp F u (d i)) → α t t' u a = y i t t' u a - (γ i t' (u ≫ G.map a) - mp F (G.map a) (γ i t u)) := by`.

Use `⟨fun t t' u a ↦ if h : ∃ i, IsUnit (mp F u (d i)) then y h.choose t t' u a - (γ h.choose t' (u ≫ G.map a) - mp F (G.map a) (γ h.choose t u)) else 0, fun i t t' u a hi ↦ ?_⟩` and prove the remaining obligations. Establish `h : ∃ i, IsUnit (mp F u (d i))` using `⟨i, hi⟩`. Simplify using `only [dif_pos h]`. Establish `k1` using `congrArg (mp F (G.map a)) (hγ i _ t u hi h.choose_spec)`. Establish `k2` using `hγ i _ t' (u ≫ G.map a) (hu a hi) (hu a h.choose_spec)`.

Establish `k3` using `he i _ _ _ u (G.map a) ⟨hi, h.choose_spec⟩`. Establish `k4` using `hβ i _ t t' u a hi h.choose_spec`. Simplify using `only [map_sub] at k1`. Take the linear combination `k1 - k2 + k3 - k4`. Use `⟨α, fun t t' t'' u a b ⟨i, hi⟩ ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[hα i _ _ _ _ hi, hα i _ _ _ _ hi, hα i _ _ _ _ (hu a hi)]`. Simplify using `only [map_sub, mp_comp, Category.assoc, G.map_comp]`. Take the linear combination `hy i t t' t'' u a b hi`.
-/
theorem twoCocycle_comma_coboundary_of_standardCover : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (n : ℕ) (d : Fin n → F.obj T), Ideal.span (Set.range d) = ⊤ → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → (∀ i : Fin n, ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u (d i)) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), (∃ i, IsUnit (mp F u (d i))) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  intro R _ C _ C' _ F G _ _ H hcov hfil T n d hd z hz hy
  choose y hy using hy
  have hu : ∀ {t t' : C'} {u : T ⟶ G.obj t} (a : t ⟶ t') {x : F.obj T}, IsUnit (mp F u x) →
      IsUnit (mp F (u ≫ G.map a) x) := fun a _ h ↦ isUnit_comp _ h
  have h1 := fun i j : Fin n ↦ GlobalTheory.T.oneCocycle_invertibleLocus_isCoboundary_alt F G H hcov hfil T (d i * d j)
    (fun t t' u a ↦ y j t t' u a - y i t t' u a) fun t t' t'' u a b h ↦ by
      rw [map_mul, IsUnit.mul_iff] at h
      rw [map_sub]
      linear_combination hy i t t' t'' u a b h.1 - hy j t t' t'' u a b h.2
  choose β hβ' using h1
  have hβ : ∀ i j t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u (d i)) →
      IsUnit (mp F u (d j)) →
      β i j t' (u ≫ G.map a) - mp F (G.map a) (β i j t u) = y j t t' u a - y i t t' u a :=
    fun i j t t' u a hi hj ↦ hβ' i j t t' u a (by rw [map_mul]; exact hi.mul hj)
  have h2 := fun i j k : Fin n ↦ GlobalTheory.T.sections_invertibleLocus_of_basisFunctor F G H hcov hfil T (d i * d j * d k)
    (fun t u ↦ β j k t u - β i k t u + β i j t u) fun t t' u a h ↦ by
      rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff] at h
      rw [map_add, map_sub]
      linear_combination hβ j k t t' u a h.1.2 h.2 - hβ i k t t' u a h.1.1 h.2 +
        hβ i j t t' u a h.1.1 h.1.2
  choose x hx' hxs' using h2
  have hx : ∀ i j k, IsSec F (fun S u ↦ (IsUnit (mp F u (d i)) ∧ IsUnit (mp F u (d j))) ∧
      IsUnit (mp F u (d k))) (x i j k) := fun i j k S S' u ψ h ↦
    hx' i j k S S' u ψ (by
      show IsUnit _
      rw [map_mul, map_mul]; exact (h.1.1.mul h.1.2).mul h.2)
  have hxs : ∀ i j k t (u : T ⟶ G.obj t), IsUnit (mp F u (d i)) → IsUnit (mp F u (d j)) →
      IsUnit (mp F u (d k)) → x i j k (G.obj t) u = β j k t u - β i k t u + β i j t u :=
    fun i j k t u hi hj hk ↦ hxs' i j k t u (by rw [map_mul, map_mul]; exact (hi.mul hj).mul hk)
  obtain ⟨e, he, he'⟩ := cech2 H hd x hx (fun l i j k S u hl hi hj hk ↦ by
    obtain ⟨m, b, hb, hb'⟩ := hcov S
    refine sep_std H hb _ fun S' ψ ⟨r, hr⟩ ↦ ?_
    obtain ⟨t, v, w, rfl⟩ := hb' r S' ψ hr
    have hl' := isUnit_comp v hl
    have hi' := isUnit_comp v hi
    have hj' := isUnit_comp v hj
    have hk' := isUnit_comp v hk
    rw [mp_comp, map_sub (mp F v), map_add (mp F v), map_sub (mp F v),
      ← hx i j k S _ u v ⟨⟨hi, hj⟩, hk⟩, ← hx l j k S _ u v ⟨⟨hl, hj⟩, hk⟩,
      ← hx l i k S _ u v ⟨⟨hl, hi⟩, hk⟩, ← hx l i j S _ u v ⟨⟨hl, hi⟩, hj⟩,
      hxs _ _ _ _ _ hi' hj' hk', hxs _ _ _ _ _ hl' hj' hk', hxs _ _ _ _ _ hl' hi' hk',
      hxs _ _ _ _ _ hl' hi' hj']
    ring_nf
    exact map_zero _)
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin n → ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ i j t u,
      IsUnit (mp F u (d i)) → IsUnit (mp F u (d j)) →
      γ j t u - γ i t u = β i j t u - e i j (G.obj t) u := by
    refine ⟨fun i t u ↦ if h : ∃ i, IsUnit (mp F u (d i)) then
      β h.choose i t u - e h.choose i _ u else 0, fun i j t u hi hj ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (d i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    linear_combination -he' _ i j _ u h.choose_spec hi hj + hxs _ i j t u h.choose_spec hi hj
  obtain ⟨α, hα⟩ : ∃ α : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ i t t' u a,
      IsUnit (mp F u (d i)) →
      α t t' u a = y i t t' u a - (γ i t' (u ≫ G.map a) - mp F (G.map a) (γ i t u)) := by
    refine ⟨fun t t' u a ↦ if h : ∃ i, IsUnit (mp F u (d i)) then
      y h.choose t t' u a - (γ h.choose t' (u ≫ G.map a) - mp F (G.map a) (γ h.choose t u)) else 0,
      fun i t t' u a hi ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (d i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    have k1 := congrArg (mp F (G.map a)) (hγ i _ t u hi h.choose_spec)
    have k2 := hγ i _ t' (u ≫ G.map a) (hu a hi) (hu a h.choose_spec)
    have k3 := he i _ _ _ u (G.map a) ⟨hi, h.choose_spec⟩
    have k4 := hβ i _ t t' u a hi h.choose_spec
    simp only [map_sub] at k1
    linear_combination k1 - k2 + k3 - k4
  refine ⟨α, fun t t' t'' u a b ⟨i, hi⟩ ↦ ?_⟩
  rw [hα i _ _ _ _ hi, hα i _ _ _ _ hi, hα i _ _ _ _ (hu a hi)]
  simp only [map_sub, mp_comp, Category.assoc, G.map_comp]
  linear_combination hy i t t' t'' u a b hi

end GlobalTheory.CatCoh.Desc
