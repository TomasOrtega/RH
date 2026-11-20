import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MultiplierIffExistsHom

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.Inertia

open GlobalTheory.WeierstrassCurve GlobalTheory.UnifCoord GlobalTheory.PeriodicWeierstrass PeriodPair GlobalTheory.CompRat.Weber

/- English proof (translation)
Take `⟨v', hv't, hv'⟩` from `exists_tangent_over f hψ hvt`. Take `⟨w, hd, -⟩` from `hu.choose_spec.choose_spec.choose_spec.2.1 v' hv't`. Take `⟨h', h1, h2, h3⟩` from `fibre_over_scheme W f hψ₀ he hv hψ hv'`. Take `⟨hw, x, y, t, hP, hx, hy, hper, heq, ht, ht0, ht1, hty, hlim⟩` from `exists_coord_eq ℂ W f PC.A (ψ ≫ ψ₀) v' h' h1 h2 h3 PC.L PC.g u w hd`. Take `⟨L', hL'⟩` from `exists_periodPair_of_lattice_in_line PC.g u.Λ w hg1 hw u.discrete u.full`.

Establish `hset : (L'.lattice : Set ℂ) = {z | z • w ∈ u.Λ}` using `Set.ext hL'`. Establish `key` using `invariants_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy) (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim`. Establish `kx` using `x_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy) (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim`. Simplify using `only [one_pow, _root_.one_mul, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆, WeierstrassCurve.map_b₂, hb, map_zero, zero_div, sub_zero] at key kx`. Use `⟨w, L', hw, hL', key.1, key.2.1, fun z => ?_⟩` and prove the remaining obligations.

Take `⟨P, hP, e1, e2, e3⟩` from `hP z`. Use `⟨P, hP, e1, by rw [e2, hL'], fun h2 => ?_⟩` and prove the remaining obligations. Rewrite using `[← e3 h2, kx _ fun hz => h2 (e2.2 ((hL' _).1 hz))]`.
-/
theorem fibre_coord (W : WeierstrassCurve ℂ) (hb : W.b₂ = 0) {P₀ : Out.PolAV (Sp ℂ)} {ψ₀ : P₀.A.left ⟶ scheme W}
    [IsIso ψ₀] (hψ₀ : ψ₀ ≫ toSpec W = P₀.A.hom) (he : eSec P₀.A ≫ ψ₀ = zero W) {v : epsR ℂ ⟶ P₀.A}
    (hvt : IsTangent v) {h : IsUnimodularSol (W.map (algebraMap ℂ (DualNumber ℂ))) ![DualNumber.eps, -1, 0]}
    (hv : v.left ≫ ψ₀ = ptHom W (algebraMap ℂ (DualNumber ℂ)) ![DualNumber.eps, -1, 0] h) (f : ℂ →+* ℂ)
    (PC : Out.PolAV (Sp ℂ)) (hg1 : PC.g = 1) (u : HolUnif PC.A PC.L PC.g) (hu : IsThetaUnif u)
    {ψ : PC.A.left ⟶ P₀.A.left} (hψ : IsGrpPullback PC.A P₀.A (spMap f) ψ) :
    ∃ (w : Fin PC.g → ℂ) (L' : PeriodPair), w ≠ 0 ∧ (∀ z, z ∈ L'.lattice ↔ z • w ∈ u.Λ) ∧
      f W.c₄ = 12 * L'.g₂ ∧ f W.c₆ = 216 * L'.g₃ ∧
      ∀ z : ℂ, ∃ (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P),
        (u.ex (z • w)).left ≫ ψ ≫ ψ₀ = ptHom W f P hP ∧ (P 2 = 0 ↔ z ∈ L'.lattice) ∧
          (P 2 ≠ 0 → ℘[L'] z * P 2 = P 0) := by
  obtain ⟨v', hv't, hv'⟩ := exists_tangent_over f hψ hvt
  obtain ⟨w, hd, -⟩ := hu.choose_spec.choose_spec.choose_spec.2.1 v' hv't
  obtain ⟨h', h1, h2, h3⟩ := fibre_over_scheme W f hψ₀ he hv hψ hv'
  obtain ⟨hw, x, y, t, hP, hx, hy, hper, heq, ht, ht0, ht1, hty, hlim⟩ :=
    exists_coord_eq ℂ W f PC.A (ψ ≫ ψ₀) v' h' h1 h2 h3 PC.L PC.g u w hd
  obtain ⟨L', hL'⟩ := exists_periodPair_of_lattice_in_line PC.g u.Λ w hg1 hw u.discrete u.full
  have hset : (L'.lattice : Set ℂ) = {z | z • w ∈ u.Λ} := Set.ext hL'
  have key := invariants_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
    (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim
  have kx := x_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
    (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim
  simp only [one_pow, _root_.one_mul, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆, WeierstrassCurve.map_b₂,
    hb, map_zero, zero_div, sub_zero] at key kx
  refine ⟨w, L', hw, hL', key.1, key.2.1, fun z => ?_⟩
  obtain ⟨P, hP, e1, e2, e3⟩ := hP z
  refine ⟨P, hP, e1, by rw [e2, hL'], fun h2 => ?_⟩
  rw [← e3 h2, kx _ fun hz => h2 (e2.2 ((hL' _).1 hz))]

/- English proof (translation)
Take `⟨Hm, χ, Ef, hA, -, -, hθ, hE, hEb⟩` from `hu`. Take `⟨Hm', χ', Ef', hA', -, -, hθ', hE', hEb'⟩` from `hu'`. Establish `hH` using `hermForm_principal_dim_one _ u.Λ w L Hm Ef g1 w0 hΛ hA.1 (hA.2.1 w w0) hE hEb`. Establish `hH'` using `hermForm_principal_dim_one _ u'.Λ w' L Hm' Ef' g2 w0' hΛ' hA'.1 (hA'.2.1 w' w0') hE' hEb'`. Take `⟨c, hc, hc1⟩` from `EllipticHom.exists_coord g1 w0`.

Set `F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ)` to `c.smulRight w'`. Establish `hF : ∀ x, F x = c x • w'` using `fun x => rfl`. Take `⟨f, hf, hFf⟩` from `exists_hom_of_linear_scaling_hermForm P Q u u' Hm χ Hm' χ' hA hA' (fun k => (hθ k).2) (fun k => (hθ' k).1) F 1 (fun l hl => by`. Rewrite using `[hF, ← hΛ']`. Conclude with `(hΛ _).2 (by rwa [hc]))`.

Use the proof step `(fun x y => by`. Establish `e` using `hH (c x) (c y)`. Rewrite `e` using `[hc, hc]`. Rewrite using `[hF, hF, hH', e, Nat.cast_one, _root_.one_mul])`. Use `⟨f, hf, fun z => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hFf, hF, map_smul, hc1, smul_eq_mul, _root_.mul_one]`.
-/
theorem exists_hom_of_lattice (P Q : Out.PolAV (Sp ℂ)) (g1 : P.g = 1) (g2 : Q.g = 1) (u : HolUnif P.A P.L P.g)
    (u' : HolUnif Q.A Q.L Q.g) (hu : IsThetaUnif u) (hu' : IsThetaUnif u') (L : PeriodPair) (w : Fin P.g → ℂ)
    (w' : Fin Q.g → ℂ) (w0 : w ≠ 0) (w0' : w' ≠ 0) (hΛ : ∀ z, z ∈ L.lattice ↔ z • w ∈ u.Λ)
    (hΛ' : ∀ z, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) :
    ∃ f : P.A ⟶ Q.A, IsMonHom f ∧ ∀ z : ℂ, u'.ex (z • w') = u.ex (z • w) ≫ f := by
  obtain ⟨Hm, χ, Ef, hA, -, -, hθ, hE, hEb⟩ := hu
  obtain ⟨Hm', χ', Ef', hA', -, -, hθ', hE', hEb'⟩ := hu'
  have hH := hermForm_principal_dim_one _ u.Λ w L Hm Ef g1 w0 hΛ hA.1 (hA.2.1 w w0) hE hEb
  have hH' := hermForm_principal_dim_one _ u'.Λ w' L Hm' Ef' g2 w0' hΛ' hA'.1 (hA'.2.1 w' w0') hE' hEb'
  obtain ⟨c, hc, hc1⟩ := EllipticHom.exists_coord g1 w0
  let F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ) := c.smulRight w'
  have hF : ∀ x, F x = c x • w' := fun x => rfl
  obtain ⟨f, hf, hFf⟩ := exists_hom_of_linear_scaling_hermForm P Q u u' Hm χ Hm' χ' hA hA'
    (fun k => (hθ k).2) (fun k => (hθ' k).1) F 1
    (fun l hl => by
      rw [hF, ← hΛ']
      exact (hΛ _).2 (by rwa [hc]))
    (fun x y => by
      have e := hH (c x) (c y)
      rw [hc, hc] at e
      rw [hF, hF, hH', e, Nat.cast_one, _root_.one_mul])
  refine ⟨f, hf, fun z => ?_⟩
  rw [← hFf, hF, map_smul, hc1, smul_eq_mul, _root_.mul_one]

/- English proof (translation)
Take `⟨f, hf, e⟩` from `exists_hom_of_lattice P Q g1 g2 u u' hu hu' L w w' w0 w0' hΛ hΛ'`. Take `⟨f', hf', e'⟩` from `exists_hom_of_lattice Q P g2 g1 u' u hu' hu L w' w w0' w0 hΛ' hΛ`. Take `⟨c, hc, -⟩` from `EllipticHom.exists_coord g1 w0`. Take `⟨c', hc', -⟩` from `EllipticHom.exists_coord g2 w0'`. Use `P.isAb.smooth` as an intermediate fact.

Use `Q.isAb.smooth` as an intermediate fact. Use `P.isAb.proper` as an intermediate fact. Use `Q.isAb.proper` as an intermediate fact. Establish `: IsReduced P.A.left` using `isReduced_of_smooth_complex _ P.A.hom inferInstance`. Establish `: IsReduced Q.A.left` using `isReduced_of_smooth_complex _ Q.A.hom inferInstance`.

Set `i : P.A ≅ Q.A` to `{ hom := f inv := f' hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by`. Take `⟨z, rfl⟩` from `u.ex_onto x`. Rewrite using `[← hc z, ← Category.assoc, ← e, ← e', Category.comp_id]`. Use `inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by`. Take `⟨z, rfl⟩` from `u'.ex_onto x`.

Rewrite using `[← hc' z, ← Category.assoc, ← e', ← e, Category.comp_id] }`. Establish `: IsMonHom i.hom` using `hf`. Conclude with `⟨_, isGrpPullback_of_iso i⟩`.
-/
theorem exists_isGrpPullback_of_lattice (P Q : Out.PolAV (Sp ℂ)) (g1 : P.g = 1) (g2 : Q.g = 1)
    (u : HolUnif P.A P.L P.g)
    (u' : HolUnif Q.A Q.L Q.g) (hu : IsThetaUnif u) (hu' : IsThetaUnif u') (L : PeriodPair) (w : Fin P.g → ℂ)
    (w' : Fin Q.g → ℂ) (w0 : w ≠ 0) (w0' : w' ≠ 0) (hΛ : ∀ z, z ∈ L.lattice ↔ z • w ∈ u.Λ)
    (hΛ' : ∀ z, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) :
    ∃ φ : P.A.left ⟶ Q.A.left, IsGrpPullback P.A Q.A (𝟙 _) φ := by
  obtain ⟨f, hf, e⟩ := exists_hom_of_lattice P Q g1 g2 u u' hu hu' L w w' w0 w0' hΛ hΛ'
  obtain ⟨f', hf', e'⟩ := exists_hom_of_lattice Q P g2 g1 u' u hu' hu L w' w w0' w0 hΛ' hΛ
  obtain ⟨c, hc, -⟩ := EllipticHom.exists_coord g1 w0
  obtain ⟨c', hc', -⟩ := EllipticHom.exists_coord g2 w0'
  have := P.isAb.smooth
  have := Q.isAb.smooth
  have := P.isAb.proper
  have := Q.isAb.proper
  have : IsReduced P.A.left := isReduced_of_smooth_complex _ P.A.hom inferInstance
  have : IsReduced Q.A.left := isReduced_of_smooth_complex _ Q.A.hom inferInstance
  let i : P.A ≅ Q.A :=
    { hom := f
      inv := f'
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u.ex_onto x
        rw [← hc z, ← Category.assoc, ← e, ← e', Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u'.ex_onto x
        rw [← hc' z, ← Category.assoc, ← e', ← e, Category.comp_id] }
  have : IsMonHom i.hom := hf
  exact ⟨_, isGrpPullback_of_iso i⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Establish `i : Fin C.P.g` using `⟨0, by rw [C.g_eq]; omega⟩`. Rewrite using `[hL, exists_wC_iff, C.lat]`. Conclude with `⟨fun ⟨m, n, h⟩ => ⟨m, n, by rw [h]⟩, fun ⟨m, n, h⟩ => ⟨m, n, mul_left_cancel₀ C.c_ne (congrFun h i)⟩⟩`.
-/
theorem mem_iff (C : Curve H) {L : PeriodPair} (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) (z : ℂ) :
    z ∈ L.lattice ↔ (fun _ => C.c * z : Fin C.P.g → ℂ) ∈ C.u.Λ := by
  have i : Fin C.P.g := ⟨0, by rw [C.g_eq]; omega⟩
  rw [hL, exists_wC_iff, C.lat]
  exact ⟨fun ⟨m, n, h⟩ => ⟨m, n, by rw [h]⟩, fun ⟨m, n, h⟩ => ⟨m, n, mul_left_cancel₀ C.c_ne (congrFun h i)⟩⟩

/- English proof (translation)
Take `⟨w, L', hw, hL', -, -, hP⟩` from `fibre_coord W hb hψ₀ he hvt hv f C.P C.g_eq C.u C.theta hψ`. Take `⟨c, hc, -⟩` from `EllipticHom.exists_coord C.g_eq hw`. Use `set m := c fun _ => C.c with hm`. Establish `e : ∀ z : ℂ, (fun _ => C.c * z : Fin C.P.g → ℂ) = (m * z) • w` using `fun z => by`. Rewrite using `[_root_.mul_comm m, ← smul_smul, hm, hc]`.

Use function extensionality and compare the values at `_`. Simplify using `[_root_.mul_comm]`. Establish `hh : IsHomothetic m L L'` using `fun x => by rw [hL', ← e, ← mem_iff C hL]`. Use `⟨(m ^ 2)⁻¹, inv_ne_zero (pow_ne_zero _ hh.ne_zero), fun z => ?_⟩` and prove the remaining obligations. Take `⟨P, hP, e1, e2, e3⟩` from `hP (m * z)`.

Use `⟨P, hP, by unfold Curve.pt; rw [e]; exact e1, by rw [e2, hh], fun h2 => ?_⟩` and prove the remaining obligations. Rewrite using `[← e3 h2, hh.weierstrassP_mul]`.
-/
theorem curve_coord (C : Curve H) {L : PeriodPair} (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s)
    (W : WeierstrassCurve ℂ) (hb : W.b₂ = 0) {P₀ : Out.PolAV (Sp ℂ)} {ψ₀ : P₀.A.left ⟶ scheme W}
    [IsIso ψ₀] (hψ₀ : ψ₀ ≫ toSpec W = P₀.A.hom) (he : eSec P₀.A ≫ ψ₀ = zero W) {v : epsR ℂ ⟶ P₀.A}
    (hvt : IsTangent v) {h : IsUnimodularSol (W.map (algebraMap ℂ (DualNumber ℂ))) ![DualNumber.eps, -1, 0]}
    (hv : v.left ≫ ψ₀ = ptHom W (algebraMap ℂ (DualNumber ℂ)) ![DualNumber.eps, -1, 0] h) (f : ℂ →+* ℂ)
    {ψ : C.P.A.left ⟶ P₀.A.left} (hψ : IsGrpPullback C.P.A P₀.A (spMap f) ψ) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ z : ℂ, ∃ (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P),
        C.pt z ≫ ψ ≫ ψ₀ = ptHom W f P hP ∧ (P 2 = 0 ↔ z ∈ L.lattice) ∧
          (P 2 ≠ 0 → lam * ℘[L] z * P 2 = P 0) := by
  obtain ⟨w, L', hw, hL', -, -, hP⟩ := fibre_coord W hb hψ₀ he hvt hv f C.P C.g_eq C.u C.theta hψ
  obtain ⟨c, hc, -⟩ := EllipticHom.exists_coord C.g_eq hw
  set m := c fun _ => C.c with hm
  have e : ∀ z : ℂ, (fun _ => C.c * z : Fin C.P.g → ℂ) = (m * z) • w := fun z => by
    rw [_root_.mul_comm m, ← smul_smul, hm, hc]
    funext _
    simp [_root_.mul_comm]
  have hh : IsHomothetic m L L' := fun x => by rw [hL', ← e, ← mem_iff C hL]
  refine ⟨(m ^ 2)⁻¹, inv_ne_zero (pow_ne_zero _ hh.ne_zero), fun z => ?_⟩
  obtain ⟨P, hP, e1, e2, e3⟩ := hP (m * z)
  refine ⟨P, hP, by unfold Curve.pt; rw [e]; exact e1, by rw [e2, hh], fun h2 => ?_⟩
  rw [← e3 h2, hh.weierstrassP_mul]

/- English proof (translation)
Set `W` to `latticeCurve L`. Establish `hb : W.b₂ = 0` using `by simp [W, latticeCurve, WeierstrassCurve.b₂]`. Establish `h4 : W.c₄ = 12 * L.g₂` using `latticeCurve_c₄ L`. Establish `h6 : W.c₆ = 216 * L.g₃`. Simplify using `only [W, latticeCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ)` using `Spec.map_id (CommRingCat.of ℂ)`. Take `⟨P₀, ψ₀, v, hg, hiso, hψ₀, he, ⟨hs, hv⟩, hlie⟩` from `exists_polAV ℂ W (latticeCurve_Δ_ne_zero L).isUnit`. Take `⟨u, hu⟩` from `exists_isThetaUnif thetaUnifAV_all P₀`. Establish `: IsMonHom (Iso.refl P₀.A).hom` using `inferInstanceAs (IsMonHom (𝟙 _))`.

Take `⟨w, L', hw, hL', e4, e6, -⟩` from `fibre_coord W hb hψ₀ he (hlie.1 0) hv (RingHom.id ℂ) P₀ hg u hu ((isGrpPullback_of_iso (Iso.refl P₀.A)).congr hid.symm rfl)`. Establish `eL : L'.lattice = L.lattice` using `lattice_eq_of_g₂_eq_of_g₃_eq (by rw [RingHom.id_apply, h4] at e4; linear_combination -e4 / 12) (by rw [RingHom.id_apply, h6] at e6; linear_combination -e6 / 216)`. Take `⟨φ, hφ⟩` from `exists_isGrpPullback_of_lattice C.P P₀ C.g_eq hg C.u u C.theta hu L (fun _ => C.c) w (fun e => C.c_ne (congrFun e ⟨0, by rw [C.g_eq]; omega⟩)) hw (fun z => by`. Rewrite using `[mem_iff C hL]`. Use `congr! 2`.

Simplify using `[_root_.mul_comm])`. Use the proof step `(fun z => by rw [← eL, hL'])`. Take `⟨l₁, hl₁, hQ⟩` from `curve_coord C hL W hb hψ₀ he (hlie.1 0) hv (RingHom.id ℂ) (hφ.congr hid.symm rfl)`. Take `⟨l₂, -, hP⟩` from `curve_coord C hL W hb hψ₀ he (hlie.1 0) hv (τ : ℂ →+* ℂ) ((h.comp hφ).congr (Category.comp_id _) rfl)`. Establish `ht : τ l₁ ≠ 0` using `by simpa using hl₁`.

Use `⟨l₂ / τ l₁, fun z z' e hz' => ?_⟩` and prove the remaining obligations. Take `⟨P, hP1, a1, a2, a3⟩` from `hP z`. Take `⟨Q, hQ1, b1, b2, b3⟩` from `hQ z'`. Establish `e2 : C.pt z ≫ (io ≫ φ) ≫ ψ₀ = spMap (τ : ℂ →+* ℂ) ≫ C.pt z' ≫ φ ≫ ψ₀`. Simplify using `only [← Category.assoc, e]`.

Establish `hτ : (τ : ℂ →+* ℂ).comp (RingHom.id ℂ) = (τ : ℂ →+* ℂ)` using `rfl`. Establish `hQ2` using `hQ1.map_comp (τ : ℂ →+* ℂ)`. Rewrite `hQ2` using `[hτ]`. Rewrite `e2` using `[a1, b1, SpecMap_ptHom, ptHom_congr W _ _ _ hτ rfl hQ2, ptHom_eq_ptHom_iff]`. Take `⟨v, hv⟩` from `e2`.

Establish `v0 : τ (Q 0) = v * P 0` using `congrFun hv 0`. Establish `v2 : τ (Q 2) = v * P 2` using `congrFun hv 2`. Establish `hQ0 : Q 2 ≠ 0` using `fun h => hz' (b2.1 h)`. Establish `hQ0' : τ (Q 2) ≠ 0` using `by simpa using hQ0`. Establish `hP0 : P 2 ≠ 0` using `right_ne_zero_of_mul (v2 ▸ hQ0')`.

Use `⟨fun h => hP0 (a2.2 h), ?_⟩` and prove the remaining obligations. Establish `e3 : τ l₁ * τ (℘[L] z') * τ (Q 2) = l₂ * ℘[L] z * τ (Q 2)`. Rewrite using `[← map_mul, ← map_mul, b3 hQ0, v0, v2, ← a3 hP0]`. Expand and normalize the polynomial expressions, which then agree. Establish `e4` using `mul_right_cancel₀ hQ0' e3`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `e4`.
-/
theorem exists_multiplier (C : Curve H) {L : PeriodPair} (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s)
    {τ : ℂ ≃+* ℂ} {io : C.P.A.left ⟶ C.P.A.left} (h : IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io) :
    ∃ a : ℂ, ∀ z z', C.pt z ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z' → z' ∉ L.lattice →
      z ∉ L.lattice ∧ τ (℘[L] z') = a * ℘[L] z := by
  let W := latticeCurve L
  have hb : W.b₂ = 0 := by simp [W, latticeCurve, WeierstrassCurve.b₂]
  have h4 : W.c₄ = 12 * L.g₂ := latticeCurve_c₄ L
  have h6 : W.c₆ = 216 * L.g₃ := by
    simp only [W, latticeCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    ring
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id (CommRingCat.of ℂ)
  obtain ⟨P₀, ψ₀, v, hg, hiso, hψ₀, he, ⟨hs, hv⟩, hlie⟩ := exists_polAV ℂ W (latticeCurve_Δ_ne_zero L).isUnit
  obtain ⟨u, hu⟩ := exists_isThetaUnif thetaUnifAV_all P₀
  have : IsMonHom (Iso.refl P₀.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  obtain ⟨w, L', hw, hL', e4, e6, -⟩ := fibre_coord W hb hψ₀ he (hlie.1 0) hv (RingHom.id ℂ) P₀ hg u hu
    ((isGrpPullback_of_iso (Iso.refl P₀.A)).congr hid.symm rfl)
  have eL : L'.lattice = L.lattice :=
    lattice_eq_of_g₂_eq_of_g₃_eq (by rw [RingHom.id_apply, h4] at e4; linear_combination -e4 / 12)
      (by rw [RingHom.id_apply, h6] at e6; linear_combination -e6 / 216)
  obtain ⟨φ, hφ⟩ := exists_isGrpPullback_of_lattice C.P P₀ C.g_eq hg C.u u C.theta hu L (fun _ => C.c) w
    (fun e => C.c_ne (congrFun e ⟨0, by rw [C.g_eq]; omega⟩)) hw
    (fun z => by
      rw [mem_iff C hL]
      congr! 2
      simp [_root_.mul_comm])
    (fun z => by rw [← eL, hL'])
  obtain ⟨l₁, hl₁, hQ⟩ := curve_coord C hL W hb hψ₀ he (hlie.1 0) hv (RingHom.id ℂ) (hφ.congr hid.symm rfl)
  obtain ⟨l₂, -, hP⟩ := curve_coord C hL W hb hψ₀ he (hlie.1 0) hv (τ : ℂ →+* ℂ)
    ((h.comp hφ).congr (Category.comp_id _) rfl)
  have ht : τ l₁ ≠ 0 := by simpa using hl₁
  refine ⟨l₂ / τ l₁, fun z z' e hz' => ?_⟩
  obtain ⟨P, hP1, a1, a2, a3⟩ := hP z
  obtain ⟨Q, hQ1, b1, b2, b3⟩ := hQ z'
  have e2 : C.pt z ≫ (io ≫ φ) ≫ ψ₀ = spMap (τ : ℂ →+* ℂ) ≫ C.pt z' ≫ φ ≫ ψ₀ := by
    simp only [← Category.assoc, e]
  have hτ : (τ : ℂ →+* ℂ).comp (RingHom.id ℂ) = (τ : ℂ →+* ℂ) := rfl
  have hQ2 := hQ1.map_comp (τ : ℂ →+* ℂ)
  rw [hτ] at hQ2
  rw [a1, b1, SpecMap_ptHom, ptHom_congr W _ _ _ hτ rfl hQ2, ptHom_eq_ptHom_iff] at e2
  obtain ⟨v, hv⟩ := e2
  have v0 : τ (Q 0) = v * P 0 := congrFun hv 0
  have v2 : τ (Q 2) = v * P 2 := congrFun hv 2
  have hQ0 : Q 2 ≠ 0 := fun h => hz' (b2.1 h)
  have hQ0' : τ (Q 2) ≠ 0 := by simpa using hQ0
  have hP0 : P 2 ≠ 0 := right_ne_zero_of_mul (v2 ▸ hQ0')
  refine ⟨fun h => hP0 (a2.2 h), ?_⟩
  have e3 : τ l₁ * τ (℘[L] z') * τ (Q 2) = l₂ * ℘[L] z * τ (Q 2) := by
    rw [← map_mul, ← map_mul, b3 hQ0, v0, v2, ← a3 hP0]
    ring
  have e4 := mul_right_cancel₀ hQ0' e3
  field_simp
  linear_combination e4

end GlobalTheory.CompRat.Inertia
