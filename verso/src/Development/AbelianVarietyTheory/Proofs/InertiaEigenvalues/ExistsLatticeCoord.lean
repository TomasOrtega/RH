import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CyclotomicCharacterEqCmMultiplierNorm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesFiniteAlgebraicPermuted
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfMapLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FixesRootOfActsTorsion

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.WeberFixed

open GlobalTheory.WeierstrassCurve GlobalTheory.UnifCoord GlobalTheory.PeriodicWeierstrass PeriodPair GlobalTheory.CompRat.Weber GlobalTheory.FieldSize

/- English proof (translation)
Take `⟨v', hv't, hv'⟩` from `exists_tangent_over f hψ htv`. Take `⟨w, hd, -⟩` from `(AnyUnif.tangent_and_unimodular thetaUnifAV_all PC u).1 v' hv't`. Take `⟨h', h1, h2, h3⟩` from `fibre_over_scheme W f hψ₀ he hv hψ hv'`. Take `⟨hw, x, y, t, hP, hx, hy, hper, heq, ht, ht0, ht1, hty, hlim⟩` from `exists_coord_eq R W f PC.A (ψ ≫ ψ₀) v' h' h1 h2 h3 PC.L PC.g u w hd`. Take `⟨L', hL'⟩` from `exists_periodPair_of_lattice_in_line PC.g u.Λ w hg1 hw u.discrete u.full`.

Establish `hset : (L'.lattice : Set ℂ) = {z | z • w ∈ u.Λ}` using `Set.ext hL'`. Establish `key` using `invariants_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy) (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim`. Establish `kx` using `x_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy) (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim`. Simplify using `only [one_pow, _root_.one_mul, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆, WeierstrassCurve.map_b₂, hb, map_zero, zero_div, sub_zero] at key kx`. Set `i : Fin PC.g` to `⟨0, by omega⟩`.

Establish `hi : ∀ j : Fin PC.g, j = i` using `fun j => Fin.ext (by have := j.2; omega)`. Establish `hwi : w i ≠ 0` using `fun h => hw (funext fun j => by rw [hi j]; exact h)`. Establish `hc : ∀ z : ℂ, (fun _ => w i * z : Fin PC.g → ℂ) = z • w` using `fun z =>`. Use function extensionality and compare the values at `fun j => by rw [hi j, Pi.smul_apply, smul_eq_mul]; ring`. Use `⟨w i, L', hwi, fun z => by rw [hc, hL'], key.1, key.2.1, fun z hz => ?_⟩` and prove the remaining obligations.

Take `⟨P, hP, e1, e2, e3⟩` from `hP z`. Establish `h2 : P 2 ≠ 0` using `fun h => hz ((hL' z).2 (e2.1 h))`. Conclude with `⟨P, hP, by rw [hc]; exact e1, h2, by rw [← e3 h2, kx _ hz]⟩`.
-/
theorem exists_lattice_coord {R : Type} [CommRing R] (W : WeierstrassCurve R) (hb : W.b₂ = 0)
    {A : Over (Sp R)} [GrpObj A] {ψ₀ : A.left ⟶ scheme W} [IsIso ψ₀]
    (hψ₀ : ψ₀ ≫ toSpec W = A.hom) (he : eSec A ≫ ψ₀ = zero W) {v : epsR R ⟶ A} (htv : IsTangent v)
    {h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0]}
    (hv : v.left ≫ ψ₀ = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h)
    (f : R →+* ℂ) (PC : Out.PolAV (Sp ℂ)) (hg1 : PC.g = 1) (u : HolUnif PC.A PC.L PC.g) {ψ : PC.A.left ⟶ A.left}
    (hψ : IsGrpPullback PC.A A (spMap f) ψ) :
    ∃ (c : ℂ) (L' : PeriodPair), c ≠ 0 ∧ (∀ z, z ∈ L'.lattice ↔ (fun _ => c * z) ∈ u.Λ) ∧
      f W.c₄ = 12 * L'.g₂ ∧ f W.c₆ = 216 * L'.g₃ ∧
      ∀ z ∉ L'.lattice, ∃ (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P),
        (u.ex fun _ => c * z).left ≫ ψ ≫ ψ₀ = ptHom W f P hP ∧ P 2 ≠ 0 ∧ ℘[L'] z * P 2 = P 0 := by
  obtain ⟨v', hv't, hv'⟩ := exists_tangent_over f hψ htv
  obtain ⟨w, hd, -⟩ := (AnyUnif.tangent_and_unimodular thetaUnifAV_all PC u).1 v' hv't
  obtain ⟨h', h1, h2, h3⟩ := fibre_over_scheme W f hψ₀ he hv hψ hv'
  obtain ⟨hw, x, y, t, hP, hx, hy, hper, heq, ht, ht0, ht1, hty, hlim⟩ :=
    exists_coord_eq R W f PC.A (ψ ≫ ψ₀) v' h' h1 h2 h3 PC.L PC.g u w hd
  obtain ⟨L', hL'⟩ := exists_periodPair_of_lattice_in_line PC.g u.Λ w hg1 hw u.discrete u.full
  have hset : (L'.lattice : Set ℂ) = {z | z • w ∈ u.Λ} := Set.ext hL'
  have key := invariants_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
    (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim
  have kx := x_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
    (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim
  simp only [one_pow, _root_.one_mul, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆, WeierstrassCurve.map_b₂,
    hb, map_zero, zero_div, sub_zero] at key kx
  let i : Fin PC.g := ⟨0, by omega⟩
  have hi : ∀ j : Fin PC.g, j = i := fun j => Fin.ext (by have := j.2; omega)
  have hwi : w i ≠ 0 := fun h => hw (funext fun j => by rw [hi j]; exact h)
  have hc : ∀ z : ℂ, (fun _ => w i * z : Fin PC.g → ℂ) = z • w := fun z =>
    funext fun j => by rw [hi j, Pi.smul_apply, smul_eq_mul]; ring
  refine ⟨w i, L', hwi, fun z => by rw [hc, hL'], key.1, key.2.1, fun z hz => ?_⟩
  obtain ⟨P, hP, e1, e2, e3⟩ := hP z
  have h2 : P 2 ≠ 0 := fun h => hz ((hL' z).2 (e2.1 h))
  exact ⟨P, hP, by rw [hc]; exact e1, h2, by rw [← e3 h2, kx _ hz]⟩

/- English proof (translation)
Generalize the expression as in `hg : P.g = g at u h`. Generalize the expression as in `hg' : Q.g = g' at u' h`. Take `rfl : g = 1` from `hg.symm.trans hP`. Take `rfl : g' = 1` from `hg'.symm.trans hQ`. Establish `hL` using `firstFiveLaws.1`.

Establish `e : ∀ (a : ℂ) (z : Fin 1 → ℂ), a ≠ 0 → z = fun _ => a * (z 0 / a)` using `fun a z ha =>`. Use function extensionality and compare the values at `fun j => by rw [Subsingleton.elim j 0, mul_div_cancel₀ _ ha]`. Take `⟨α, hα, hα'⟩` from `exists_isMonHom_of_map_lattice thetaUnifAV_all hL P Q 1 u u' ((c' / c) • LinearMap.id) hP hQ fun z hz => by`. Rewrite `hz` using `[e c z hc, h]`. Use `hz using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `j`. Rewrite using `[Subsingleton.elim j 0]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Take `⟨β, -, hβ'⟩` from `exists_isMonHom_of_map_lattice thetaUnifAV_all hL Q P 1 u' u ((c / c') • LinearMap.id) hQ hP fun z hz => by`.

Rewrite `hz` using `[e c' z hc', ← h]`. Use `hz using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Rewrite using `[Subsingleton.elim j 0]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Use `P.isAb.smooth` as an intermediate fact. Use `Q.isAb.smooth` as an intermediate fact. Use `P.isAb.proper` as an intermediate fact. Use `Q.isAb.proper` as an intermediate fact.

Establish `: IsReduced P.A.left` using `isReduced_of_smooth_complex _ P.A.hom inferInstance`. Establish `: IsReduced Q.A.left` using `isReduced_of_smooth_complex _ Q.A.hom inferInstance`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply] at hα' hβ'`. Set `ψ : P.A ≅ Q.A` to `{ hom := α inv := β hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by`. Take `⟨z, rfl⟩` from `u.ex_onto x`.

Rewrite using `[← Category.assoc, ← hα', ← hβ', smul_smul, show c / c' * (c' / c) = 1 by field_simp, one_smul, Category.comp_id]`. Use `inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by`. Take `⟨z, rfl⟩` from `u'.ex_onto x`. Rewrite using `[← Category.assoc, ← hβ', ← hα', smul_smul, show c' / c * (c / c') = 1 by field_simp, one_smul, Category.comp_id] }`. Establish `: IsMonHom ψ.hom` using `hα`.

Conclude with `⟨_, isGrpPullback_of_iso ψ⟩`.
-/
theorem exists_iso (P Q : Out.PolAV (Sp ℂ)) (hP : P.g = 1) (hQ : Q.g = 1) (u : HolUnif P.A P.L P.g)
    (u' : HolUnif Q.A Q.L Q.g) {c c' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : ∀ z, (fun _ => c * z) ∈ u.Λ ↔ (fun _ => c' * z) ∈ u'.Λ) :
    ∃ ψ : P.A.left ⟶ Q.A.left, IsGrpPullback P.A Q.A (𝟙 _) ψ := by
  generalize hg : P.g = g at u h
  generalize hg' : Q.g = g' at u' h
  obtain rfl : g = 1 := hg.symm.trans hP
  obtain rfl : g' = 1 := hg'.symm.trans hQ
  have hL := firstFiveLaws.1
  have e : ∀ (a : ℂ) (z : Fin 1 → ℂ), a ≠ 0 → z = fun _ => a * (z 0 / a) := fun a z ha =>
    funext fun j => by rw [Subsingleton.elim j 0, mul_div_cancel₀ _ ha]
  obtain ⟨α, hα, hα'⟩ := exists_isMonHom_of_map_lattice thetaUnifAV_all hL P Q 1 u u' ((c' / c) • LinearMap.id)
    hP hQ fun z hz => by
      rw [e c z hc, h] at hz
      convert hz using 1
      funext j
      rw [Subsingleton.elim j 0]
      simp
      ring
  obtain ⟨β, -, hβ'⟩ := exists_isMonHom_of_map_lattice thetaUnifAV_all hL Q P 1 u' u ((c / c') • LinearMap.id)
    hQ hP fun z hz => by
      rw [e c' z hc', ← h] at hz
      convert hz using 1
      funext j
      rw [Subsingleton.elim j 0]
      simp
      ring
  have := P.isAb.smooth
  have := Q.isAb.smooth
  have := P.isAb.proper
  have := Q.isAb.proper
  have : IsReduced P.A.left := isReduced_of_smooth_complex _ P.A.hom inferInstance
  have : IsReduced Q.A.left := isReduced_of_smooth_complex _ Q.A.hom inferInstance
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hα' hβ'
  let ψ : P.A ≅ Q.A :=
    { hom := α
      inv := β
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u.ex_onto x
        rw [← Category.assoc, ← hα', ← hβ', smul_smul, show c / c' * (c' / c) = 1 by field_simp, one_smul,
          Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u'.ex_onto x
        rw [← Category.assoc, ← hβ', ← hα', smul_smul, show c' / c * (c / c') = 1 by field_simp, one_smul,
          Category.comp_id] }
  have : IsMonHom ψ.hom := hα
  exact ⟨_, isGrpPullback_of_iso ψ⟩

/- English proof (translation)
Establish `hD` using `g₂_cube_sub_g₃_sq_ne_zero L`. Establish `e : L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 = (m ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)`. Rewrite using `[h.g₂_eq, h.g₃_eq]`. Clear the denominators using the available nonvanishing facts. Use `⟨?_, fun z => ?_⟩` and prove the remaining obligations.

Rewrite using `[e, h.g₂_eq]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, h.g₂_eq, h.g₃_eq, h.weierstrassP_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem weber_homothetic {L L' : PeriodPair} {m : ℂ} (hm : m ≠ 0) (h : IsHomothetic m L L') :
    L'.g₂ ^ 3 / (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ∧
      ∀ z, L'.g₂ * L'.g₃ / (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) * ℘[L'] (m * z) =
        L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * ℘[L] z := by
  have hD := g₂_cube_sub_g₃_sq_ne_zero L
  have e : L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 = (m ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [h.g₂_eq, h.g₃_eq]; field_simp
  refine ⟨?_, fun z => ?_⟩
  · rw [e, h.g₂_eq]; field_simp
  · rw [e, h.g₂_eq, h.g₃_eq, h.weierstrassP_mul]; field_simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Take `⟨C, io, hio, hact⟩` from `hτ`. Set `W : WeierstrassCurve ℂ` to `⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩`. Establish `hb : W.b₂ = 0` using `by simp [W, WeierstrassCurve.b₂]`. Establish `h4 : W.c₄ = 12 * L.g₂`. Simplify using `only [W, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h6 : W.c₆ = 216 * L.g₃`. Simplify using `only [W, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]`. Expand and normalize the polynomial expressions, which then agree. Establish `hΔ : IsUnit W.Δ`.

Use `isUnit_iff_ne_zero.2 fun h => g₂_cube_sub_g₃_sq_ne_zero L ?_` and prove the remaining obligations. Establish `e` using `W.c_relation`. Rewrite `e` using `[h, h4, h6]`. Take the linear combination `-e / 1728`. Take `⟨P₀, ψ₀, v, hg, hiso, hψ₀, he, ⟨h, hv⟩, hlie⟩` from `exists_polAV ℂ W hΔ`.

Establish `hid : spMap (RingHom.id ℂ) = 𝟙 _` using `Spec.map_id (CommRingCat.of ℂ)`. Establish `: IsMonHom (Iso.refl P₀.A).hom` using `inferInstanceAs (IsMonHom (𝟙 _))`. Take `⟨u₀, -⟩` from `exists_isThetaUnif thetaUnifAV_all P₀`. Take `⟨c₀, L₀, hc₀, hL₀, a4, a6, -⟩` from `exists_lattice_coord W hb hψ₀ he (hlie.1 0) hv (RingHom.id ℂ) P₀ hg u₀ ((isGrpPullback_of_iso (Iso.refl P₀.A)).congr hid.symm rfl)`. Establish `e₀ : L₀.lattice = L.lattice` using `lattice_eq_of_g₂_eq_of_g₃_eq (by rw [RingHom.id_apply, h4] at a4; linear_combination -a4 / 12) (by rw [RingHom.id_apply, h6] at a6; linear_combination -a6 / 216)`.

Establish `i : Fin C.P.g` using `⟨0, by rw [C.g_eq]; omega⟩`. Establish `hC : ∀ z, (fun _ => C.c * z) ∈ C.u.Λ ↔ z ∈ L.lattice` using `fun z => by`. Rewrite using `[CurveEndo.mem_lattice, hL]`. Conclude with `exists_congr fun a => ⟨fun h => mul_left_cancel₀ C.c_ne (congrFun h i), fun h => by rw [h]⟩`. Take `⟨ψ, hψ⟩` from `exists_iso C.P P₀ C.g_eq hg C.u u₀ C.c_ne hc₀ fun z => by rw [hC, ← hL₀, e₀]`.

Take `⟨c₁, L₁, hc₁, hL₁, b4, b6, hb₁⟩` from `exists_lattice_coord W hb hψ₀ he (hlie.1 0) hv (RingHom.id ℂ) C.P C.g_eq C.u (hψ.congr hid.symm rfl)`. Take `⟨c₂, L₂, hc₂, hL₂, d4, d6, hb₂⟩` from `exists_lattice_coord W hb hψ₀ he (hlie.1 0) hv (τ : ℂ →+* ℂ) C.P C.g_eq C.u ((hio.comp hψ).congr (Category.comp_id _) rfl)`. Establish `hc` using `C.c_ne`. Establish `H₁ : IsHomothetic (C.c / c₁) L L₁` using `fun x => by`. Rewrite using `[hL₁, ← hC, ← _root_.mul_assoc, mul_div_cancel₀ _ hc₁]`.

Establish `H₂ : IsHomothetic (C.c / c₂) L L₂` using `fun x => by`. Rewrite using `[hL₂, ← hC, ← _root_.mul_assoc, mul_div_cancel₀ _ hc₂]`. Take `⟨j₁, w₁⟩` from `weber_homothetic (div_ne_zero hc hc₁) H₁`. Take `⟨j₂, w₂⟩` from `weber_homothetic (div_ne_zero hc hc₂) H₂`. Rewrite `b4`, `b6` using `[RingHom.id_apply]`.

Establish `t2 : τ L₁.g₂ = L₂.g₂`. Rewrite `d4` using `[b4, map_mul, map_ofNat]`. Conclude with `mul_left_cancel₀ (by norm_num) d4`. Establish `t3 : τ L₁.g₃ = L₂.g₃`. Rewrite `d6` using `[b6, map_mul, map_ofNat]`.

Conclude with `mul_left_cancel₀ (by norm_num) d6`. Introduce and unpack `_ (rfl | ⟨z, hz, hz', rfl⟩)`. Use `conv_lhs => rw [← j₁]`. Rewrite using `[← j₂]`. Simplify using `[map_div₀, t2, t3, map_ofNat]`.

Take `⟨s, rfl⟩` from `(hL z).1 hz`. Take `⟨Q, hQ1, b1, hQ0, b3⟩` from `hb₁ _ fun h => hz' ((H₁ _).1 h)`. Take `⟨P, hP1, a1, hP0, a3⟩` from `hb₂ _ fun h => hz' ((H₂ _).1 h)`. Establish `e` using `hact s`. Rewrite `e` using `[show wC H (1, 0) = 1 by simp [wC], _root_.one_mul]`.

Simplify using `only [← _root_.mul_assoc, mul_div_cancel₀ _ hc₁] at b1`. Simplify using `only [← _root_.mul_assoc, mul_div_cancel₀ _ hc₂] at a1`. Establish `e2 : ptHom W (τ : ℂ →+* ℂ) P hP1 = spMap (τ : ℂ →+* ℂ) ≫ ptHom W (RingHom.id ℂ) Q hQ1`. Rewrite using `[← a1, ← b1]`. Establish `e3` using `congrArg (· ≫ ψ ≫ ψ₀) e`.

Simplify using `only [Category.assoc] at e3 ⊢`. Conclude with `e3`. Establish `hQ2` using `hQ1.map_comp (τ : ℂ →+* ℂ)`. Rewrite `hQ2` using `[RingHom.comp_id]`. Rewrite `e2` using `[SpecMap_ptHom, ptHom_congr W _ _ _ (RingHom.comp_id _) rfl hQ2, ptHom_eq_ptHom_iff]`.

Take `⟨k, hk⟩` from `e2`. Establish `v0 : τ (Q 0) = k * P 0` using `congrFun hk 0`. Establish `v2 : τ (Q 2) = k * P 2` using `congrFun hk 2`. Establish `hQ0' : τ (Q 2) ≠ 0` using `by simpa using hQ0`. Establish `tp : τ (℘[L₁] (C.c / c₁ * (wC H s / n))) = ℘[L₂] (C.c / c₂ * (wC H s / n))`.

Use `mul_right_cancel₀ hQ0' ?_` and prove the remaining obligations. Rewrite using `[← map_mul, b3, v0, v2, ← a3]`. Expand and normalize the polynomial expressions, which then agree. Use `conv_lhs => rw [← w₁]`. Rewrite using `[← w₂, map_mul, tp]`.

Simplify using `[map_div₀, t2, t3, map_ofNat]`.
-/
theorem weber_fixed (H : Host E) (L : PeriodPair) (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) {τ : ℂ ≃+* ℂ} {n : ℕ}
    (hτ : FixesCurve H τ n) : ∀ x ∈ weberSet L n, τ x = x := by
  obtain ⟨C, io, hio, hact⟩ := hτ
  let W : WeierstrassCurve ℂ := ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩
  have hb : W.b₂ = 0 := by simp [W, WeierstrassCurve.b₂]
  have h4 : W.c₄ = 12 * L.g₂ := by
    simp only [W, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring
  have h6 : W.c₆ = 216 * L.g₃ := by
    simp only [W, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]; ring
  have hΔ : IsUnit W.Δ := by
    refine isUnit_iff_ne_zero.2 fun h => g₂_cube_sub_g₃_sq_ne_zero L ?_
    have e := W.c_relation
    rw [h, h4, h6] at e
    linear_combination -e / 1728
  obtain ⟨P₀, ψ₀, v, hg, hiso, hψ₀, he, ⟨h, hv⟩, hlie⟩ := exists_polAV ℂ W hΔ
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id (CommRingCat.of ℂ)
  have : IsMonHom (Iso.refl P₀.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  obtain ⟨u₀, -⟩ := exists_isThetaUnif thetaUnifAV_all P₀
  obtain ⟨c₀, L₀, hc₀, hL₀, a4, a6, -⟩ := exists_lattice_coord W hb hψ₀ he (hlie.1 0) hv (RingHom.id ℂ) P₀ hg u₀
    ((isGrpPullback_of_iso (Iso.refl P₀.A)).congr hid.symm rfl)
  have e₀ : L₀.lattice = L.lattice := lattice_eq_of_g₂_eq_of_g₃_eq
    (by rw [RingHom.id_apply, h4] at a4; linear_combination -a4 / 12)
    (by rw [RingHom.id_apply, h6] at a6; linear_combination -a6 / 216)
  have i : Fin C.P.g := ⟨0, by rw [C.g_eq]; omega⟩
  have hC : ∀ z, (fun _ => C.c * z) ∈ C.u.Λ ↔ z ∈ L.lattice := fun z => by
    rw [CurveEndo.mem_lattice, hL]
    exact exists_congr fun a => ⟨fun h => mul_left_cancel₀ C.c_ne (congrFun h i), fun h => by rw [h]⟩
  obtain ⟨ψ, hψ⟩ := exists_iso C.P P₀ C.g_eq hg C.u u₀ C.c_ne hc₀ fun z => by rw [hC, ← hL₀, e₀]
  obtain ⟨c₁, L₁, hc₁, hL₁, b4, b6, hb₁⟩ := exists_lattice_coord W hb hψ₀ he (hlie.1 0) hv (RingHom.id ℂ) C.P C.g_eq
    C.u (hψ.congr hid.symm rfl)
  obtain ⟨c₂, L₂, hc₂, hL₂, d4, d6, hb₂⟩ := exists_lattice_coord W hb hψ₀ he (hlie.1 0) hv (τ : ℂ →+* ℂ) C.P C.g_eq
    C.u ((hio.comp hψ).congr (Category.comp_id _) rfl)
  have hc := C.c_ne
  have H₁ : IsHomothetic (C.c / c₁) L L₁ := fun x => by
    rw [hL₁, ← hC, ← _root_.mul_assoc, mul_div_cancel₀ _ hc₁]
  have H₂ : IsHomothetic (C.c / c₂) L L₂ := fun x => by
    rw [hL₂, ← hC, ← _root_.mul_assoc, mul_div_cancel₀ _ hc₂]
  obtain ⟨j₁, w₁⟩ := weber_homothetic (div_ne_zero hc hc₁) H₁
  obtain ⟨j₂, w₂⟩ := weber_homothetic (div_ne_zero hc hc₂) H₂
  rw [RingHom.id_apply] at b4 b6
  have t2 : τ L₁.g₂ = L₂.g₂ := by
    rw [b4, map_mul, map_ofNat] at d4
    exact mul_left_cancel₀ (by norm_num) d4
  have t3 : τ L₁.g₃ = L₂.g₃ := by
    rw [b6, map_mul, map_ofNat] at d6
    exact mul_left_cancel₀ (by norm_num) d6
  rintro _ (rfl | ⟨z, hz, hz', rfl⟩)
  · conv_lhs => rw [← j₁]
    rw [← j₂]
    simp [map_div₀, t2, t3, map_ofNat]
  obtain ⟨s, rfl⟩ := (hL z).1 hz
  obtain ⟨Q, hQ1, b1, hQ0, b3⟩ := hb₁ _ fun h => hz' ((H₁ _).1 h)
  obtain ⟨P, hP1, a1, hP0, a3⟩ := hb₂ _ fun h => hz' ((H₂ _).1 h)
  have e := hact s
  rw [show wC H (1, 0) = 1 by simp [wC], _root_.one_mul] at e
  simp only [← _root_.mul_assoc, mul_div_cancel₀ _ hc₁] at b1
  simp only [← _root_.mul_assoc, mul_div_cancel₀ _ hc₂] at a1
  have e2 : ptHom W (τ : ℂ →+* ℂ) P hP1 = spMap (τ : ℂ →+* ℂ) ≫ ptHom W (RingHom.id ℂ) Q hQ1 := by
    rw [← a1, ← b1]
    have e3 := congrArg (· ≫ ψ ≫ ψ₀) e
    simp only [Category.assoc] at e3 ⊢
    exact e3
  have hQ2 := hQ1.map_comp (τ : ℂ →+* ℂ)
  rw [RingHom.comp_id] at hQ2
  rw [SpecMap_ptHom, ptHom_congr W _ _ _ (RingHom.comp_id _) rfl hQ2, ptHom_eq_ptHom_iff] at e2
  obtain ⟨k, hk⟩ := e2
  have v0 : τ (Q 0) = k * P 0 := congrFun hk 0
  have v2 : τ (Q 2) = k * P 2 := congrFun hk 2
  have hQ0' : τ (Q 2) ≠ 0 := by simpa using hQ0
  have tp : τ (℘[L₁] (C.c / c₁ * (wC H s / n))) = ℘[L₂] (C.c / c₂ * (wC H s / n)) := by
    refine mul_right_cancel₀ hQ0' ?_
    rw [← map_mul, b3, v0, v2, ← a3]
    ring
  conv_lhs => rw [← w₁]
  rw [← w₂, map_mul, tp]
  simp [map_div₀, t2, t3, map_ofNat]

/- English proof (translation)
Take `⟨C, io, h⟩` from `hτ`. Simplify using `using MultiplierNorm.map_zeta_eq_zpow_norm E H C τ (CurveConjCompare.fixes_root_of_acts_torsion hn h) io n (1, 0) (by omega) h`.
-/
theorem zeta_fixed (H : Host E) {τ : ℂ ≃+* ℂ} {n : ℕ} (hn : 2 ≤ n) (hτ : FixesCurve H τ n) : τ (zeta n) = zeta n := by
  obtain ⟨C, io, h⟩ := hτ
  simpa using MultiplierNorm.map_zeta_eq_zpow_norm E H C τ (CurveConjCompare.fixes_root_of_acts_torsion hn h) io n (1, 0)
    (by omega) h

end GlobalTheory.WeberFixed
