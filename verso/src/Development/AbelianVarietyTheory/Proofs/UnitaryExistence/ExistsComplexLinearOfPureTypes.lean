import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in

/- English proof (translation)
Use `set L : Submodule ℤ V := P.range.toIntSubmodule with hL`. Use `haveI : DiscreteTopology L := hd`. Use `haveI : IsZLattice ℝ L := ⟨by simpa [hL] using hs⟩`. Set `b` to `Module.Free.chooseBasis ℤ L`. Set `e : A ≃+ P.range` to `AddMonoidHom.ofInjective hi`.

Set `r : V →ₗ[ℝ] W` to `(b.ofZLatticeBasis ℝ L).constr ℝ (fun i => Q (e.symm (b i)))`. Use `⟨r, fun a => ?_⟩` and prove the remaining obligations. Set `f₁ : L →+ W` to `r.toAddMonoidHom.comp L.subtype.toAddMonoidHom`. Set `f₂ : L →+ W` to `Q.comp e.symm.toAddMonoidHom`. Establish `hf : f₁.toIntLinearMap = f₂.toIntLinearMap`.

Use `b.ext fun i => ?_` and prove the remaining obligations. Use `show r (b i : V) = Q (e.symm (b i))`. Rewrite using `[← Module.Basis.ofZLatticeBasis_apply ℝ L b i]`. Conclude with `(b.ofZLatticeBasis ℝ L).constr_basis ℝ (fun i => Q (e.symm (b i))) i`. Establish `h : r (P a) = Q (e.symm ⟨P a, a, rfl⟩)` using `LinearMap.congr_fun hf ⟨P a, a, rfl⟩`.

Establish `he : e.symm ⟨P a, a, rfl⟩ = a`. Rewrite using `[AddEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Rewrite using `[h, he]`.
-/
theorem _root_.GlobalTheory.CompRat.exists_real_extension_of_lattice {A V W : Type} [AddCommGroup A] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] (P : A →+ V) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) (Q : A →+ W) :
    ∃ r : V →ₗ[ℝ] W, ∀ a, r (P a) = Q a := by
  set L : Submodule ℤ V := P.range.toIntSubmodule with hL
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by simpa [hL] using hs⟩
  let b := Module.Free.chooseBasis ℤ L
  let e : A ≃+ P.range := AddMonoidHom.ofInjective hi
  let r : V →ₗ[ℝ] W := (b.ofZLatticeBasis ℝ L).constr ℝ (fun i => Q (e.symm (b i)))
  refine ⟨r, fun a => ?_⟩
  let f₁ : L →+ W := r.toAddMonoidHom.comp L.subtype.toAddMonoidHom
  let f₂ : L →+ W := Q.comp e.symm.toAddMonoidHom
  have hf : f₁.toIntLinearMap = f₂.toIntLinearMap := by
    refine b.ext fun i => ?_
    show r (b i : V) = Q (e.symm (b i))
    rw [← Module.Basis.ofZLatticeBasis_apply ℝ L b i]
    exact (b.ofZLatticeBasis ℝ L).constr_basis ℝ (fun i => Q (e.symm (b i))) i
  have h : r (P a) = Q (e.symm ⟨P a, a, rfl⟩) := LinearMap.congr_fun hf ⟨P a, a, rfl⟩
  have he : e.symm ⟨P a, a, rfl⟩ = a := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  rw [h, he]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
/- English proof (translation)
Introduce `E _ _ _ H D D' g ty P P' hP hP' Φ hsplit h₁ h₂`. Establish `hP₀` using `hP`. Establish `hP'₀` using `hP'`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod at hP₀ hP'₀`. Take `⟨-, hi, hd, hs, -⟩` from `hP₀`.

Take `⟨-, hi', hd', hs', -⟩` from `hP'₀`. Take `⟨r, hr⟩` from `_root_.GlobalTheory.CompRat.exists_real_extension_of_lattice P hi hd hs (P'.comp Φ.toLinearMap.toAddMonoidHom)`. Take `⟨r', hr'⟩` from `_root_.GlobalTheory.CompRat.exists_real_extension_of_lattice P' hi' hd' hs' (P.comp Φ.symm.toLinearMap.toAddMonoidHom)`. Establish `hr₁ : ∀ a, r (P a) = P' (Φ a)` using `hr`. Establish `hr'₁ : ∀ b, r' (P' b) = P (Φ.symm b)` using `hr'`.

Establish `him : H.rt0.im ≠ 0`. Introduce `h0`. Establish `hsq : (H.rt0 ^ 2).re = H.rt0.re ^ 2` using `by simp [pow_two, Complex.mul_re, h0]`. Rewrite `hsq` using `[H.sqrt_neg_disc_sq]`. Establish `h2 : (2 : ℝ) ≤ H.d` using `by exact_mod_cast H.d_prime.two_le`.

Simplify using `at hsq`. Use polynomial arithmetic with `[sq_nonneg H.rt0.re]`. Establish `hsplit' : _root_.GlobalTheory.PureType.lat hP H.rt0 ⊔ _root_.GlobalTheory.PureType.lat hP (-H.rt0) = ⊤` using `hsplit`. Establish `hkey : ∀ a, r (H.rt0 • P a) = H.rt0 • r (P a)`. Introduce `a`.

Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 (hsplit' ▸ Submodule.mem_top : a ∈ _)`. Establish `ry : r (H.rt0 • P y) = H.rt0 • r (P y)`. Rewrite using `[← _root_.GlobalTheory.PureType.period_rt_smul hP hy, hr₁, hr₁, map_smul, _root_.GlobalTheory.PureType.period_rt_smul hP' (h₁ y hy)]`. Establish `rz : r (-H.rt0 • P z) = -H.rt0 • r (P z)`. Rewrite using `[← _root_.GlobalTheory.PureType.period_rt_smul hP hz, hr₁, hr₁, map_smul, _root_.GlobalTheory.PureType.period_rt_smul hP' (h₂ z hz)]`.

Establish `rz' : r (H.rt0 • P z) = H.rt0 • r (P z)`. Rewrite `rz` using `[neg_smul, map_neg, neg_smul, neg_inj]`. Conclude with `rz`. Simplify using `only [map_add, smul_add, ry, rz']`. Establish `hrot : ∀ v, r (H.rt0 • v) = H.rt0 • r v`.

Establish `hext : r.comp (H.rt0 • LinearMap.id) = (H.rt0 • LinearMap.id).comp r` using `LinearMap.ext_on_range hs fun a => by simpa using hkey a`. Introduce `v`. Simplify using `using LinearMap.congr_fun hext v`. Establish `hlin : ∀ (c : ℂ) v, r (c • v) = c • r v`. Introduce `c v`.

Establish `hc : c = ((c.re - c.im / H.rt0.im * H.rt0.re : ℝ) : ℂ) + ((c.im / H.rt0.im : ℝ) : ℂ) * H.rt0`. Apply the tactic sequence `apply Complex.ext <;> simp <;> field_simp <;> ring`. Rewrite using `[hc, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, map_add, map_smul, map_smul, hrot, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]`. Establish `hl : ∀ v, r' (r v) = v`. Establish `hext : r'.comp r = LinearMap.id` using `LinearMap.ext_on_range hs fun a => by simp [hr₁, hr'₁]`.

Conclude with `fun v => LinearMap.congr_fun hext v`. Establish `hrr : ∀ w, r (r' w) = w`. Establish `hext : r.comp r' = LinearMap.id` using `LinearMap.ext_on_range hs' fun b => by simp [hr₁, hr'₁]`. Conclude with `fun w => LinearMap.congr_fun hext w`. Set `L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)` to `{ toFun := r, map_add' := r.map_add, map_smul' := hlin }`.

Conclude with `⟨LinearEquiv.ofBijective L ⟨Function.LeftInverse.injective (g := r') hl, fun w => ⟨r' w, hrr w⟩⟩, fun a => (hr₁ a).symm⟩`.
-/
theorem _root_.GlobalTheory.CompRat.exists_complex_linear_of_pure_types : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D D' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) (hP' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D' ty P') (Φ : D.La ≃ₗ[𝓞 E] D'.La), _root_.GlobalTheory.CompRat.IsSplit hP → (∀ a ∈ _root_.GlobalTheory.PureType.lat hP H.rt0, Φ a ∈ _root_.GlobalTheory.PureType.lat hP' H.rt0) → (∀ a ∈ _root_.GlobalTheory.PureType.lat hP (-H.rt0), Φ a ∈ _root_.GlobalTheory.PureType.lat hP' (-H.rt0)) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' (Φ a) = L (P a) := by
  intro E _ _ _ H D D' g ty P P' hP hP' Φ hsplit h₁ h₂
  have hP₀ := hP
  have hP'₀ := hP'
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod at hP₀ hP'₀
  obtain ⟨-, hi, hd, hs, -⟩ := hP₀
  obtain ⟨-, hi', hd', hs', -⟩ := hP'₀
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.CompRat.exists_real_extension_of_lattice P hi hd hs
    (P'.comp Φ.toLinearMap.toAddMonoidHom)
  obtain ⟨r', hr'⟩ := _root_.GlobalTheory.CompRat.exists_real_extension_of_lattice P' hi' hd' hs'
    (P.comp Φ.symm.toLinearMap.toAddMonoidHom)
  have hr₁ : ∀ a, r (P a) = P' (Φ a) := hr
  have hr'₁ : ∀ b, r' (P' b) = P (Φ.symm b) := hr'
  have him : H.rt0.im ≠ 0 := by
    intro h0
    have hsq : (H.rt0 ^ 2).re = H.rt0.re ^ 2 := by simp [pow_two, Complex.mul_re, h0]
    rw [H.sqrt_neg_disc_sq] at hsq
    have h2 : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    simp at hsq
    nlinarith [sq_nonneg H.rt0.re]
  have hsplit' : _root_.GlobalTheory.PureType.lat hP H.rt0 ⊔ _root_.GlobalTheory.PureType.lat hP (-H.rt0) = ⊤ :=
    hsplit
  have hkey : ∀ a, r (H.rt0 • P a) = H.rt0 • r (P a) := by
    intro a
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hsplit' ▸ Submodule.mem_top : a ∈ _)
    have ry : r (H.rt0 • P y) = H.rt0 • r (P y) := by
      rw [← _root_.GlobalTheory.PureType.period_rt_smul hP hy, hr₁, hr₁, map_smul,
        _root_.GlobalTheory.PureType.period_rt_smul hP' (h₁ y hy)]
    have rz : r (-H.rt0 • P z) = -H.rt0 • r (P z) := by
      rw [← _root_.GlobalTheory.PureType.period_rt_smul hP hz, hr₁, hr₁, map_smul,
        _root_.GlobalTheory.PureType.period_rt_smul hP' (h₂ z hz)]
    have rz' : r (H.rt0 • P z) = H.rt0 • r (P z) := by
      rw [neg_smul, map_neg, neg_smul, neg_inj] at rz
      exact rz
    simp only [map_add, smul_add, ry, rz']
  have hrot : ∀ v, r (H.rt0 • v) = H.rt0 • r v := by
    have hext : r.comp (H.rt0 • LinearMap.id) = (H.rt0 • LinearMap.id).comp r :=
      LinearMap.ext_on_range hs fun a => by simpa using hkey a
    intro v
    simpa using LinearMap.congr_fun hext v
  have hlin : ∀ (c : ℂ) v, r (c • v) = c • r v := by
    intro c v
    have hc : c = ((c.re - c.im / H.rt0.im * H.rt0.re : ℝ) : ℂ) +
        ((c.im / H.rt0.im : ℝ) : ℂ) * H.rt0 := by
      apply Complex.ext <;> simp <;> field_simp <;> ring
    rw [hc, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, map_add, map_smul, map_smul,
      hrot, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  have hl : ∀ v, r' (r v) = v := by
    have hext : r'.comp r = LinearMap.id :=
      LinearMap.ext_on_range hs fun a => by simp [hr₁, hr'₁]
    exact fun v => LinearMap.congr_fun hext v
  have hrr : ∀ w, r (r' w) = w := by
    have hext : r.comp r' = LinearMap.id :=
      LinearMap.ext_on_range hs' fun b => by simp [hr₁, hr'₁]
    exact fun w => LinearMap.congr_fun hext w
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := r, map_add' := r.map_add, map_smul' := hlin }
  exact ⟨LinearEquiv.ofBijective L ⟨Function.LeftInverse.injective (g := r') hl,
    fun w => ⟨r' w, hrr w⟩⟩, fun a => (hr₁ a).symm⟩

end GlobalTheory.CompRat
