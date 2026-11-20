import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.DualLattices.ProdDvdOfIso

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
  {F : Type} [Field F]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_aug {X : Type} [AddCommGroup X] {M : Submodule R (X → C)} {g : X → C} :
    g ∈ augIdeal M ↔ g ∈ M ∧ g 0 = 0 := Iff.rfl

section Pull

variable {X Y : Type} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]

/- English proof (translation)
Use `hg.2 0 0` as an intermediate fact. Rewrite `this` using `[smul_zero, MulChar.map_zero, map_zero, zero_mul]`. Then use the resulting hypothesis.
-/
theorem eig_zero {M : Submodule R (X → C)} {χ : MulChar F R} {g : X → C} (hg : g ∈ eig M χ) :
    g 0 = 0 := by
  have := hg.2 0 0
  rwa [smul_zero, MulChar.map_zero, map_zero, zero_mul] at this

/- English proof (translation)
Assemble the required witnesses or components as `⟨h g hg.1, fun a x => by simpa using hg.2 a (u x)⟩`.
-/
theorem eig_pull (u : X →ₗ[F] Y) {M : Submodule R (Y → C)} {M' : Submodule R (X → C)}
    (h : ∀ g ∈ M, g ∘ u ∈ M') {χ : MulChar F R} {g : Y → C} (hg : g ∈ eig M χ) :
    g ∘ u ∈ eig M' χ :=
  ⟨h g hg.1, fun a x => by simpa using hg.2 a (u x)⟩

/- English proof (translation)
Establish `: (sqIdeal (augIdeal M)).map (LinearMap.funLeft R C u) ≤ sqIdeal (augIdeal M')`. Rewrite using `[sqIdeal, Submodule.map_span_le]`. Introduce and unpack `_ ⟨a, ha, b, hb, rfl⟩`. Use `Submodule.subset_span ⟨a ∘ u, ⟨h a ha.1, ?_⟩, b ∘ u, ⟨h b hb.1, ?_⟩, rfl⟩` and prove the remaining obligations. Use `show a (u 0) = 0`.

Rewrite using `[map_zero]`. Conclude with `ha.2`. Use `show b (u 0) = 0`. Rewrite using `[map_zero]`. Conclude with `hb.2`.

Conclude with `this (Submodule.mem_map_of_mem hg)`.
-/
theorem sq_pull (u : X →ₗ[F] Y) {M : Submodule R (Y → C)} {M' : Submodule R (X → C)}
    (h : ∀ g ∈ M, g ∘ u ∈ M') {g : Y → C} (hg : g ∈ sqIdeal (augIdeal M)) :
    g ∘ u ∈ sqIdeal (augIdeal M') := by
  have : (sqIdeal (augIdeal M)).map (LinearMap.funLeft R C u) ≤ sqIdeal (augIdeal M') := by
    rw [sqIdeal, Submodule.map_span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine Submodule.subset_span ⟨a ∘ u, ⟨h a ha.1, ?_⟩, b ∘ u, ⟨h b hb.1, ?_⟩, rfl⟩
    · show a (u 0) = 0
      rw [map_zero]; exact ha.2
    · show b (u 0) = 0
      rw [map_zero]; exact hb.2
  exact this (Submodule.mem_map_of_mem hg)

/- English proof (translation)
Establish `h1 : ∀ g ∈ M, g ∘ (e : X →ₗ[F] Y) ∈ M'` using `fun g hg => (h g).1 hg`. Establish `c1 : ∀ g : X → C, (g ∘ (e.symm : Y →ₗ[F] X)) ∘ e = g` using `fun g => by`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Establish `c2 : ∀ g : Y → C, (g ∘ e) ∘ (e.symm : Y →ₗ[F] X) = g` using `fun g => by`.

Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Establish `h2 : ∀ g ∈ M', g ∘ (e.symm : Y →ₗ[F] X) ∈ M` using `fun g hg => by`. Rewrite using `[h, c1]`. Conclude with `hg`.

Set `φ : eig M χ ≃ₗ[R] eig M' χ` to `{ toFun := fun g => ⟨g.1 ∘ e, eig_pull (e : X →ₗ[F] Y) h1 g.2⟩ invFun := fun g => ⟨g.1 ∘ (e.symm : Y →ₗ[F] X), eig_pull _ h2 g.2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl left_inv := fun g => Subtype.ext (c2 g.1) right_inv := fun g => Subtype.ext (c1 g.1) }`. Take `⟨m, c, ⟨ψ⟩, hx⟩` from `hx`. Use `⟨m, c, ⟨(Submodule.Quotient.equiv _ _ φ ?_).trans ψ⟩, hx⟩` and prove the remaining obligations. Use extensionality with `g`. Rewrite using `[Submodule.mem_map_equiv]`.

Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `: (g.1 ∘ (e.symm : Y →ₗ[F] X)) ∘ e ∈ sqIdeal (augIdeal M')` using `sq_pull (e : X →ₗ[F] Y) h1 hg`. Rewrite `this` using `[c1]`. Conclude with `this`.

Introduce `hg`. Conclude with `sq_pull (e.symm : Y →ₗ[F] X) h2 hg`.
-/
theorem hasLen_transport (e : X ≃ₗ[F] Y) {M : Submodule R (Y → C)} {M' : Submodule R (X → C)}
    (h : ∀ g, g ∈ M ↔ g ∘ e ∈ M') {χ : MulChar F R} {x : NNReal}
    (hx : HasLen v R (OmType M' χ) x) : HasLen v R (OmType M χ) x := by
  have h1 : ∀ g ∈ M, g ∘ (e : X →ₗ[F] Y) ∈ M' := fun g hg => (h g).1 hg
  have c1 : ∀ g : X → C, (g ∘ (e.symm : Y →ₗ[F] X)) ∘ e = g := fun g => by
    funext x; simp
  have c2 : ∀ g : Y → C, (g ∘ e) ∘ (e.symm : Y →ₗ[F] X) = g := fun g => by
    funext x; simp
  have h2 : ∀ g ∈ M', g ∘ (e.symm : Y →ₗ[F] X) ∈ M := fun g hg => by
    rw [h, c1]; exact hg
  let φ : eig M χ ≃ₗ[R] eig M' χ :=
    { toFun := fun g => ⟨g.1 ∘ e, eig_pull (e : X →ₗ[F] Y) h1 g.2⟩
      invFun := fun g => ⟨g.1 ∘ (e.symm : Y →ₗ[F] X), eig_pull _ h2 g.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun g => Subtype.ext (c2 g.1)
      right_inv := fun g => Subtype.ext (c1 g.1) }
  obtain ⟨m, c, ⟨ψ⟩, hx⟩ := hx
  refine ⟨m, c, ⟨(Submodule.Quotient.equiv _ _ φ ?_).trans ψ⟩, hx⟩
  ext g
  rw [Submodule.mem_map_equiv]
  constructor
  · intro hg
    have : (g.1 ∘ (e.symm : Y →ₗ[F] X)) ∘ e ∈ sqIdeal (augIdeal M') :=
      sq_pull (e : X →ₗ[F] Y) h1 hg
    rw [c1] at this
    exact this
  · intro hg
    exact sq_pull (e.symm : Y →ₗ[F] X) h2 hg

end Pull

variable {N : Type} [AddCommGroup N] [Module F N]

/- English proof (translation)
Establish `: Subsingleton (eig M χ)` using `⟨fun a b => Subtype.ext (funext fun y => by`. Rewrite using `[Subsingleton.elim y 0, eig_zero a.2, eig_zero b.2])⟩`. Establish `: Subsingleton (OmType M χ)` using `(Submodule.Quotient.mk_surjective _).subsingleton`. Use `hasLen_unique hv hx ⟨0, Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩, by simp⟩` and prove the remaining obligations.
-/
theorem hasLen_trivial (hv : v.Integers R) [Subsingleton N] {M : Submodule R (N → C)}
    {χ : MulChar F R} {x : NNReal} (hx : HasLen v R (OmType M χ) x) : x = 1 := by
  have : Subsingleton (eig M χ) := ⟨fun a b => Subtype.ext (funext fun y => by
    rw [Subsingleton.elim y 0, eig_zero a.2, eig_zero b.2])⟩
  have : Subsingleton (OmType M χ) := (Submodule.Quotient.mk_surjective _).subsingleton
  refine hasLen_unique hv hx ⟨0, Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩, by simp⟩

/- English proof (translation)
Use extensionality with `h`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, ⟨hg, hi⟩, rfl⟩`. Use `⟨g ∘ L.mkQ, ⟨hg, fun x k hk => ?_⟩, ?_⟩` and prove the remaining obligations. Use `show g (L.mkQ (x + k)) = g (L.mkQ x)`.

Rewrite using `[map_add]`. Conclude with `hi _ _ (Submodule.mem_map_of_mem hk)`. Use function extensionality and compare the values at `a show g (L.mkQ (a • t)) = g (a • L.mkQ t)`. Rewrite using `[map_smul]`. Introduce and unpack `⟨g, ⟨hg, hi⟩, rfl⟩`.

Establish `hsur` using `L.mkQ_surjective`. Establish `key : ∀ x, g (Function.surjInv hsur (L.mkQ x)) = g x` using `fun x => by`. Establish `h1 : L.mkQ (Function.surjInv hsur (L.mkQ x) - x) = 0`. Rewrite using `[map_sub, Function.surjInv_eq hsur, sub_self]`. Establish `h2 : Function.surjInv hsur (L.mkQ x) - x ∈ K` using `hLK ((Submodule.Quotient.mk_eq_zero L).1 h1)`.

Use `hi x _ h2` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Use `⟨g ∘ Function.surjInv hsur, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show (fun x => g (Function.surjInv hsur (L.mkQ x))) ∈ M`. Simplify `hg` using `only [key]`.

Introduce and unpack `x _ ⟨k, hk, rfl⟩`. Take `⟨x, rfl⟩` from `hsur x`. Use `show g (Function.surjInv hsur (L.mkQ x + L.mkQ k)) = g (Function.surjInv hsur (L.mkQ x))`. Rewrite using `[← map_add, key, key]`. Conclude with `hi x k hk`.

Use function extensionality and compare the values at `a show g (Function.surjInv hsur (a • L.mkQ t)) = g (a • t)`. Rewrite using `[← map_smul, key]`.
-/
theorem quot_step (M : Submodule R (N → C)) {L K : Submodule F N} (hLK : L ≤ K) (t : N) :
    stepOrder (M.comap (LinearMap.funLeft R C (L.mkQ : N → N ⧸ L))) (K.map L.mkQ) (L.mkQ t) =
      stepOrder M K t := by
  ext h
  constructor
  · rintro ⟨g, ⟨hg, hi⟩, rfl⟩
    refine ⟨g ∘ L.mkQ, ⟨hg, fun x k hk => ?_⟩, ?_⟩
    · show g (L.mkQ (x + k)) = g (L.mkQ x)
      rw [map_add]
      exact hi _ _ (Submodule.mem_map_of_mem hk)
    · funext a
      show g (L.mkQ (a • t)) = g (a • L.mkQ t)
      rw [map_smul]
  · rintro ⟨g, ⟨hg, hi⟩, rfl⟩
    have hsur := L.mkQ_surjective
    have key : ∀ x, g (Function.surjInv hsur (L.mkQ x)) = g x := fun x => by
      have h1 : L.mkQ (Function.surjInv hsur (L.mkQ x) - x) = 0 := by
        rw [map_sub, Function.surjInv_eq hsur, sub_self]
      have h2 : Function.surjInv hsur (L.mkQ x) - x ∈ K :=
        hLK ((Submodule.Quotient.mk_eq_zero L).1 h1)
      have := hi x _ h2
      rwa [add_sub_cancel] at this
    refine ⟨g ∘ Function.surjInv hsur, ⟨?_, ?_⟩, ?_⟩
    · show (fun x => g (Function.surjInv hsur (L.mkQ x))) ∈ M
      simpa only [key] using hg
    · rintro x _ ⟨k, hk, rfl⟩
      obtain ⟨x, rfl⟩ := hsur x
      show g (Function.surjInv hsur (L.mkQ x + L.mkQ k)) = g (Function.surjInv hsur (L.mkQ x))
      rw [← map_add, key, key]
      exact hi x k hk
    · funext a
      show g (Function.surjInv hsur (a • L.mkQ t)) = g (a • t)
      rw [← map_smul, key]

/- English proof (translation)
Use extensionality with `h`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨g, hg, rfl⟩, e⟩`. Conclude with `⟨g, hg, fun a k hk => e a ⟨k, hKL hk⟩ hk⟩`. Introduce and unpack `⟨g, hg, e⟩`.

Conclude with `⟨_, ⟨g, hg, rfl⟩, fun a k hk => e a k hk⟩`.
-/
theorem sub_stepRes (M : Submodule R (N → C)) {L K : Submodule F N} (hKL : K ≤ L) (t : L) :
    stepOrderRes (M.map (LinearMap.funLeft R C (Subtype.val : L → N))) (K.comap L.subtype) t =
      stepOrderRes M K (t : N) := by
  ext h
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, e⟩
    exact ⟨g, hg, fun a k hk => e a ⟨k, hKL hk⟩ hk⟩
  · rintro ⟨g, hg, e⟩
    exact ⟨_, ⟨g, hg, rfl⟩, fun a k hk => e a k hk⟩

/- English proof (translation)
Use `hasLen_transport (LinearEquiv.toSpanNonzeroSingleton F N t ht) (fun g => ?_) hx` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩`. Use `⟨g, ⟨hg, fun x k hk => ?_⟩, rfl⟩` and prove the remaining obligations. Take `rfl : k = 0` from `hk`.

Rewrite using `[add_zero]`. Introduce and unpack `⟨g', ⟨hg, -⟩, e⟩`. Use `⟨g', hg, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Take `⟨a, rfl⟩` from `(LinearEquiv.toSpanNonzeroSingleton F N t ht).surjective y`.

Conclude with `congrFun e a`.
-/
theorem hasLen_line (M : Submodule R (N → C)) {t : N} (ht : t ≠ 0) {χ : MulChar F R} {x : NNReal}
    (hx : HasLen v R (OmType (stepOrder M (⊥ : Submodule F N) t) χ) x) :
    HasLen v R (OmType (M.map (LinearMap.funLeft R C
      (Subtype.val : Submodule.span F {t} → N))) χ) x := by
  refine hasLen_transport (LinearEquiv.toSpanNonzeroSingleton F N t ht) (fun g => ?_) hx
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g, ⟨hg, fun x k hk => ?_⟩, rfl⟩
    obtain rfl : k = 0 := hk
    rw [add_zero]
  · rintro ⟨g', ⟨hg, -⟩, e⟩
    refine ⟨g', hg, ?_⟩
    funext y
    obtain ⟨a, rfl⟩ := (LinearEquiv.toSpanNonzeroSingleton F N t ht).surjective y
    exact congrFun e a

end PositivityTheory.HtPt.Rd
