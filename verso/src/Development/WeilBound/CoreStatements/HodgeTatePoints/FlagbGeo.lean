import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver

noncomputable section

namespace PositivityTheory.HtPt.Flagb

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Take `⟨u, rfl⟩` from `hu`. Use `⟨(u.isUnit.map _).ne_zero, ⟨_, rfl⟩, ⟨(u⁻¹ : _ˣ), map_units_inv _ u⟩⟩` and prove the remaining obligations.
-/
theorem unitAt_of_isUnit (q : Cpt ξ) (u : X.presheaf.stalk q.1) (hu : IsUnit u) : unitAt ξ q (genMap ξ q u) := by
  obtain ⟨u, rfl⟩ := hu
  refine ⟨(u.isUnit.map _).ne_zero, ⟨_, rfl⟩, ⟨(u⁻¹ : _ˣ), map_units_inv _ u⟩⟩

def secMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (hg : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.germ U (ξ (IsLocalRing.closedPoint Ω)) hg).hom

/- English proof (translation)
Take `⟨q, h⟩` from `q`. Use `X.presheaf.germ_stalkSpecializes_apply (x := ξ (IsLocalRing.closedPoint Ω)) hq h f` as an intermediate fact. Conclude with `congrArg (Scheme.stalkClosedPointTo ξ).hom this`.
-/
theorem genMap_germ (q : Cpt ξ) (U : X.Opens) (hq : q.1 ∈ U) (hg : genPt ξ ∈ U) (f : Γ(X, U)) :
    genMap ξ q ((X.presheaf.germ U q.1 hq).hom f) = secMap ξ U hg f := by
  obtain ⟨q, h⟩ := q
  have := X.presheaf.germ_stalkSpecializes_apply (x := ξ (IsLocalRing.closedPoint Ω)) hq h f
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom this

/- English proof (translation)
Take `⟨U, hU, hUm⟩` from `tie.affine c hc`. Establish `hreg : ∀ a : Ω, a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩`. Introduce `a`. Take `⟨s, hs⟩` from `tie.gen.bij.2 a`. Use `⟨s, ?_⟩` and prove the remaining obligations.

Unfold `genMap`. Establish `: X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _` using `X.presheaf.stalkSpecializes_refl _`. Use `erw [this, Category.id_comp]`. Conclude with `hs`. Establish `hg : genPt ξ ∈ U` using `(hUm _).2 ⟨specializes_rfl, hc, fun c' => hreg _⟩`.

Set `ψ : Γ(X, U) →+* Ω` to `secMap ξ U hg`. Establish `hψ : ∀ (q : Cpt ξ) (hq : q.1 ∈ U) (f : Γ(X, U)), genMap ξ q ((X.presheaf.germ U q.1 hq).hom f) = ψ f`. Introduce `q hq f`. Conclude with `genMap_germ q U hq hg f`. Establish `hψA : ∀ f, ψ f ∈ A`.

Introduce `f`. Establish `h1 : ψ f ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)` using `(tie.ring c hc _).2 fun q hq => ⟨_, hψ q ((hUm _).2 ⟨q.2, hq⟩) f⟩`. Establish `h2 : Algebra.adjoin ℤ (Set.range fun j => x j / x c) ≤ subalgebraOfSubring A.toSubring` using `Algebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact hA j)`. Conclude with `h2 h1`. Set `ψA : Γ(X, U) →+* A` to `ψ.codRestrict A hψA`.

Set `𝔭 : PrimeSpectrum Γ(X, U)` to `⟨m.comap ψA, inferInstance⟩`. Establish `hq : hU.fromSpec 𝔭 ∈ U`. Establish `: hU.fromSpec 𝔭 ∈ Set.range hU.fromSpec` using `⟨_, rfl⟩`. Rewrite `this` using `[hU.range_fromSpec]`. Then use the resulting hypothesis. Take `⟨hs, hin⟩` from `(hUm _).1 hq`.

Use `letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec 𝔭)) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec 𝔭, hq⟩`. Establish `hloc : IsLocalization 𝔭.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec 𝔭))` using `hU.isLocalization_stalk' 𝔭 hq`. Establish `hal : ∀ f, genMap ξ ⟨_, hs⟩ (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec 𝔭)) f) = ψ f` using `fun f => hψ ⟨_, hs⟩ hq f`. Use `⟨⟨_, hs⟩, hin, ?_, fun n hn => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨z, rfl⟩`.

Take `⟨⟨a, s⟩, h⟩` from `IsLocalization.surj (S := X.presheaf.stalk (hU.fromSpec 𝔭)) 𝔭.asIdeal.primeCompl z`. Use `⟨ψA s, s.2, ψA a, ?_⟩` and prove the remaining obligations. Use `congrArg (genMap ξ ⟨_, hs⟩) h` as an intermediate fact. Rewrite `this` using `[map_mul, hal, hal]`. Conclude with `(mul_comm _ _).trans this`.

Establish `hn' : (n : Γ(X, U)) ∈ 𝔭.asIdeal.primeCompl` using `by show ψA n ∉ m`. Rewrite using `[map_natCast]` and apply the resulting hypothesis. Use `unitAt_of_isUnit ⟨_, hs⟩ _ (IsLocalization.map_units (X.presheaf.stalk (hU.fromSpec 𝔭)) ⟨_, hn'⟩)` as an intermediate fact. Rewrite `this` using `[hal, map_natCast]`. Then use the resulting hypothesis.
-/
theorem exists_point {κ : Type} {x : κ → Ω} (tie : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0) {o : Type} [CommRing o]
    [Algebra o Ω] (A : Subalgebra o Ω) (hA : ∀ j, x j / x c ∈ A) (m : Ideal A) [hm : m.IsPrime] :
    ∃ q : Cpt ξ, InChart ξ x c q ∧ (∀ z ∈ regAt ξ q, ∃ s ∉ m, ∃ a : A, (s : Ω) * z = a) ∧
      ∀ n : ℕ, (n : A) ∉ m → unitAt ξ q (n : Ω) := by
  obtain ⟨U, hU, hUm⟩ := tie.affine c hc
  have hreg : ∀ a : Ω, a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
    intro a
    obtain ⟨s, hs⟩ := tie.gen.bij.2 a
    refine ⟨s, ?_⟩
    unfold genMap
    have : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
      X.presheaf.stalkSpecializes_refl _
    erw [this, Category.id_comp]
    exact hs
  have hg : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, hc, fun c' => hreg _⟩
  let ψ : Γ(X, U) →+* Ω := secMap ξ U hg
  have hψ : ∀ (q : Cpt ξ) (hq : q.1 ∈ U) (f : Γ(X, U)), genMap ξ q ((X.presheaf.germ U q.1 hq).hom f) = ψ f := by
    intro q hq f
    exact genMap_germ q U hq hg f
  have hψA : ∀ f, ψ f ∈ A := by
    intro f
    have h1 : ψ f ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) :=
      (tie.ring c hc _).2 fun q hq => ⟨_, hψ q ((hUm _).2 ⟨q.2, hq⟩) f⟩
    have h2 : Algebra.adjoin ℤ (Set.range fun j => x j / x c) ≤ subalgebraOfSubring A.toSubring :=
      Algebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact hA j)
    exact h2 h1
  let ψA : Γ(X, U) →+* A := ψ.codRestrict A hψA
  let 𝔭 : PrimeSpectrum Γ(X, U) := ⟨m.comap ψA, inferInstance⟩
  have hq : hU.fromSpec 𝔭 ∈ U := by
    have : hU.fromSpec 𝔭 ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rwa [hU.range_fromSpec] at this
  obtain ⟨hs, hin⟩ := (hUm _).1 hq
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec 𝔭)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec 𝔭, hq⟩
  have hloc : IsLocalization 𝔭.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec 𝔭)) :=
    hU.isLocalization_stalk' 𝔭 hq
  have hal : ∀ f, genMap ξ ⟨_, hs⟩ (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec 𝔭)) f) = ψ f :=
    fun f => hψ ⟨_, hs⟩ hq f
  refine ⟨⟨_, hs⟩, hin, ?_, fun n hn => ?_⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (S := X.presheaf.stalk (hU.fromSpec 𝔭)) 𝔭.asIdeal.primeCompl z
    refine ⟨ψA s, s.2, ψA a, ?_⟩
    have := congrArg (genMap ξ ⟨_, hs⟩) h
    rw [map_mul, hal, hal] at this
    exact (mul_comm _ _).trans this
  · have hn' : (n : Γ(X, U)) ∈ 𝔭.asIdeal.primeCompl := by
      show ψA n ∉ m
      rwa [map_natCast]
    have := unitAt_of_isUnit ⟨_, hs⟩ _ (IsLocalization.map_units (X.presheaf.stalk (hU.fromSpec 𝔭)) ⟨_, hn'⟩)
    rwa [hal, map_natCast] at this

/- English proof (translation)
Proceed by induction on `n using induction_on_primes with`. Consider the case `zero => exact absurd rfl hn`. Consider the case `one => exact ⟨by simp, by simpa using one_mem _, by simpa using one_mem _⟩`. Consider the case `prime_mul p a hp ih`. Establish `h1` using `h p hp (dvd_mul_right _ _)`.

Establish `h2` using `ih (right_ne_zero_of_mul hn) fun r hr hd => h r hr (hd.mul_left _)`. Rewrite using `[Nat.cast_mul]`. Conclude with `⟨mul_ne_zero h1.1 h2.1, mul_mem h1.2.1 h2.2.1, by rw [mul_inv]; exact mul_mem h1.2.2 h2.2.2⟩`.
-/
theorem unitAt_nat (q : Cpt ξ) (n : ℕ) (hn : n ≠ 0) (h : ∀ r : ℕ, r.Prime → r ∣ n → unitAt ξ q (r : Ω)) :
    unitAt ξ q (n : Ω) := by
  induction n using induction_on_primes with
  | zero => exact absurd rfl hn
  | one => exact ⟨by simp, by simpa using one_mem _, by simpa using one_mem _⟩
  | prime_mul p a hp ih =>
    have h1 := h p hp (dvd_mul_right _ _)
    have h2 := ih (right_ne_zero_of_mul hn) fun r hr hd => h r hr (hd.mul_left _)
    rw [Nat.cast_mul]
    exact ⟨mul_ne_zero h1.1 h2.1, mul_mem h1.2.1 h2.2.1, by rw [mul_inv]; exact mul_mem h1.2.2 h2.2.2⟩

/- English proof (translation)
Proceed by induction on `he using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨v, h1, h2⟩` from `hx`. Use `Submodule.subset_span ⟨v ≫ f, ?_, ?_⟩` and prove the remaining obligations. Unfold `IsTanAt at h1 ⊢`.

Rewrite using `[Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, MonObj.one_comp]`. Rewrite using `[hT x, Over.comp_left, Over.comp_left, h2]`. Conclude with `Category.assoc _ _ _`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx`. Establish `: T (c • x) = c • T x` using `map_smul T (c : Ω) x`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem lat_stable {G : Over X} [GrpObj G] {L : Type} [AddCommGroup L] [Module Ω L] (M : LieModel G ξ L)
    (f : G ⟶ G) [IsMonHom f] (T : L →ₗ[Ω] L) (hT : M.IsDiffOf f T) (q : Cpt ξ) (e : L) (he : e ∈ M.lat q) :
    T e ∈ M.lat q := by
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, h1, h2⟩ := hx
    refine Submodule.subset_span ⟨v ≫ f, ?_, ?_⟩
    · unfold IsTanAt at h1 ⊢
      rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, MonObj.one_comp]
    · rw [hT x, Over.comp_left, Over.comp_left, h2]
      exact Category.assoc _ _ _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have : T (c • x) = c • T x := map_smul T (c : Ω) x
    rw [this]; exact Submodule.smul_mem _ c hx

end PositivityTheory.HtPt.Flagb
