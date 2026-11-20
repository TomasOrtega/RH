import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsionTheta

/- English proof (translation)
Unfold `ptMap`. Use `ext1`. Simplify using `only [Over.comp_left, Over.homMk_left]`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem ptMap_comp_ptMap {O : Type} [CommRing O] {A B C : Type} [CommRing A] [Algebra O A]
    [CommRing B] [Algebra O B] [CommRing C] [Algebra O C] (φ : A →ₐ[O] B) (ψ : B →ₐ[O] C) :
    ptMap ψ ≫ ptMap φ = ptMap (ψ.comp φ) := by
  unfold ptMap
  ext1
  simp only [Over.comp_left, Over.homMk_left]
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Introduce `h0`. Set `b` to `Module.Free.chooseBasis O H`. Establish `hex : ∃ i, IsUnit (b.repr l i)`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`.

Apply `hl` to reduce the goal to its premises. Rewrite using `[← b.sum_repr l]`. Use `Ideal.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 (hne i)))`.

Take `⟨i, hi⟩` from `hex`. Establish `h1` using `congrArg (fun x => TensorProduct.lid O K (TensorProduct.map (b.coord i) LinearMap.id x)) h0`. Simplify using `only [TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, map_zero, Module.Basis.coord_apply] at h1`. Rewrite `h1` using `[Algebra.smul_def, _root_.mul_one]`. Conclude with `(hi.map (algebraMap O K)).ne_zero h1`.
-/
theorem tmul_one_ne_zero {O : Type} [CommRing O] [IsLocalRing O] {H : Type} [CommRing H]
    [Algebra O H] [Module.Finite O H] [Module.Free O H] (l : H)
    (hl : l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H))
    (K : Type) [Field K] [Algebra O K] : l ⊗ₜ[O] (1 : K) ≠ 0 := by
  classical
  intro h0
  let b := Module.Free.chooseBasis O H
  have hex : ∃ i, IsUnit (b.repr l i) := by
    by_contra hne
    push Not at hne
    apply hl
    rw [← b.sum_repr l]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 (hne i)))
  obtain ⟨i, hi⟩ := hex
  have h1 := congrArg (fun x => TensorProduct.lid O K (TensorProduct.map (b.coord i) LinearMap.id x)) h0
  simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, map_zero,
    Module.Basis.coord_apply] at h1
  rw [Algebra.smul_def, _root_.mul_one] at h1
  exact (hi.map (algebraMap O K)).ne_zero h1

/- English proof (translation)
Rewrite using `[← ptMap_comp_ptMap, Category.assoc]`.
-/
private lemma ptMap_comp_comp {O : Type} [CommRing O] {A B C : Type} [CommRing A] [Algebra O A]
    [CommRing B] [Algebra O B] [CommRing C] [Algebra O C] {X : Over (Sp O)} (φ : A →ₐ[O] B)
    (ψ : B →ₐ[O] C) (f : specO O A ⟶ X) : ptMap (ψ.comp φ) ≫ f = ptMap ψ ≫ ptMap φ ≫ f := by
  rw [← ptMap_comp_ptMap, Category.assoc]

/- English proof (translation)
Introduce `O _ _ G _ _ n H _ _ _ _ y hy hU ε l c hε hann hεl hlm`. Establish `tors : ∀ (S : Type) [CommRing S] [Algebra O S] (f : specO O S ⟶ specO O H), (f ≫ y) ^ n = 1`. Introduce `S _ _ f`. Rewrite using `[← comp_pow, hy, comp_one]`. Establish `uniq : ∀ (S : Type) [CommRing S] [Algebra O S] (φ₁ φ₂ : H →ₐ[O] S), ptMap φ₁ ≫ y = ptMap φ₂ ≫ y → φ₁ = φ₂`.

Introduce `S _ _ φ₁ φ₂ h`. Take `⟨φ, -, hφ⟩` from `hU S (ptMap φ₂ ≫ y) (tors S _)`. Conclude with `(hφ φ₁ h).trans (hφ φ₂ rfl).symm`. Set `iL : H →ₐ[O] H ⊗[O] H` to `Algebra.TensorProduct.includeLeft`. Set `iR : H →ₐ[O] H ⊗[O] H` to `Algebra.TensorProduct.includeRight`.

Take `⟨d, hd, -⟩` from `hU (H ⊗[O] H) (ptMap iL ≫ y * (ptMap iR ≫ y)⁻¹) (by rw [mul_pow, inv_pow, tors, tors, inv_one, _root_.mul_one])`. Take `⟨m, hm, -⟩` from `hU (H ⊗[O] H) (ptMap iL ≫ y * ptMap iR ≫ y) (by rw [mul_pow, tors, tors, _root_.mul_one])`. Set `eH : H →ₐ[O] H` to `(Algebra.ofId O H).comp ε`. Establish `heH : ptMap eH ≫ y = 1`. Rewrite using `[ptMap_comp_comp, hε, comp_one]`.

Establish `hmd : (Algebra.TensorProduct.lmul' O : H ⊗[O] H →ₐ[O] H).comp d = eH`. Apply `uniq` to reduce the goal to its premises. Rewrite using `[ptMap_comp_comp, hd, comp_mul, GrpObj.comp_inv, ← ptMap_comp_comp, ← ptMap_comp_comp, heH]`. Establish `h1 : (Algebra.TensorProduct.lmul' O : H ⊗[O] H →ₐ[O] H).comp iL = AlgHom.id O H`. Use extensionality with `x`.

Simplify using `[iL]`. Establish `h2 : (Algebra.TensorProduct.lmul' O : H ⊗[O] H →ₐ[O] H).comp iR = AlgHom.id O H`. Use extensionality with `x`. Simplify using `[iR]`. Rewrite using `[h1, h2, mul_inv_cancel]`.

Use `⟨d l, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hl' : ∀ a : H, a * l = algebraMap O H (ε a) * l`. Introduce `a`. Use `hann (a - algebraMap O H (ε a)) (by simp)` as an intermediate fact. Rewrite `this` using `[sub_mul, sub_eq_zero]`. Then use the resulting hypothesis.

Set `e2 : H ⊗[O] H →ₐ[O] H` to `Algebra.TensorProduct.lift eH (AlgHom.id O H) (fun _ _ => Commute.all _ _)`. Establish `hkey : ∀ x : H ⊗[O] H, x * (l ⊗ₜ[O] (1 : H)) = (l ⊗ₜ[O] (1 : H)) * ((1 : H) ⊗ₜ[O] e2 x)`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a b`. Simplify using `only [e2, eH, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul, hl' a, AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.id_apply]`. Rewrite using `[← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]`. Consider the case `add x x' hx hx' => rw [add_mul, hx, hx', map_add, TensorProduct.tmul_add, mul_add]`. Set `ψ : H ⊗[O] H →ₐ[O] H ⊗[O] H` to `Algebra.TensorProduct.lift d iR (fun _ _ => Commute.all _ _)`.

Establish `hψL : ψ.comp iL = d` using `by ext x; simp [ψ, iL]`. Establish `hψR : ψ.comp iR = iR` using `by ext x; simp [ψ, iR]`. Establish `he2L : e2.comp iL = eH` using `by ext x; simp [e2, iL]`. Establish `he2R : e2.comp iR = AlgHom.id O H` using `by ext x; simp [e2, iR]`. Establish `he2m : e2.comp m = AlgHom.id O H`.

Apply `uniq` to reduce the goal to its premises. Rewrite using `[ptMap_comp_comp, hm, comp_mul, ← ptMap_comp_comp, ← ptMap_comp_comp, he2L, he2R, heH, _root_.one_mul]`. Establish `hψm : ψ.comp m = iL`. Apply `uniq` to reduce the goal to its premises. Rewrite using `[ptMap_comp_comp, hm, comp_mul, ← ptMap_comp_comp, ← ptMap_comp_comp, hψL, hψR, hd, inv_mul_cancel_right]`.

Introduce `h`. Establish `a1 : h ⊗ₜ[O] (1 : H) = ψ (m h)`. Rewrite using `[← AlgHom.comp_apply, hψm]`. Both sides reduce to the same expression. Establish `a2 : d l = ψ (l ⊗ₜ[O] (1 : H))` using `by simp [ψ]`.

Establish `a3 : (1 : H) ⊗ₜ[O] h = ψ ((1 : H) ⊗ₜ[O] h)` using `by simp [ψ, iR]`. Establish `a4 : e2 (m h) = h` using `by rw [← AlgHom.comp_apply, he2m]; rfl`. Rewrite using `[a1, a2, ← map_mul, hkey, a4, map_mul, ← a3, ← a2, _root_.mul_comm]`. Use `DFunLike.congr_fun hmd l` as an intermediate fact. Rewrite `this` using `[AlgHom.comp_apply]`.

Rewrite using `[this]`. Simplify using `[eH, hεl]`. Introduce `K _ _ _ _ ga`. Set `jL : H →ₐ[O] H ⊗[O] K` to `Algebra.TensorProduct.includeLeft`. Set `jR : K →ₐ[O] H ⊗[O] K` to `Algebra.TensorProduct.includeRight`.

Set `κ : H ⊗[O] H →ₐ[O] H ⊗[O] K` to `Algebra.TensorProduct.map (AlgHom.id O H) ga`. Set `Sg : H →ₐ[O] H ⊗[O] K` to `κ.comp m`. Set `MainNotions : H ⊗[O] K →ₐ[O] H ⊗[O] K` to `Algebra.TensorProduct.lift Sg jR (fun _ _ => Commute.all _ _)`. Establish `hκL : κ.comp iL = jL` using `by ext x; simp [κ, iL, jL]`. Establish `hκR : κ.comp iR = jR.comp ga` using `by ext x; simp [κ, iR, jR]`.

Establish `hSL : (MainNotions.comp κ).comp iL = Sg` using `by ext x; simp [MainNotions, κ, iL]`. Establish `hSR : (MainNotions.comp κ).comp iR = jR.comp ga` using `by ext x; simp [MainNotions, κ, iR, jR]`. Establish `hSg : ptMap Sg ≫ y = ptMap jL ≫ y * ptMap (jR.comp ga) ≫ y`. Rewrite using `[ptMap_comp_comp, hm, comp_mul, ← ptMap_comp_comp, ← ptMap_comp_comp, hκL, hκR]`. Establish `hback : (MainNotions.comp κ).comp d = jL`.

Apply `uniq` to reduce the goal to its premises. Rewrite using `[ptMap_comp_comp, hd, comp_mul, GrpObj.comp_inv, ← ptMap_comp_comp, ← ptMap_comp_comp, hSL, hSR, hSg, mul_inv_cancel_right]`. Introduce `h0`. Apply `tmul_one_ne_zero l hlm K` to reduce the goal to its premises. Use `DFunLike.congr_fun hback l` as an intermediate fact.

Simplify using `only [AlgHom.comp_apply] at this`. Express the relevant statement in the definitionally equal form `MainNotions (κ (d l)) = l ⊗ₜ[O] (1 : K) at this`. Rewrite using `[← this]`. Express the relevant statement in the definitionally equal form `MainNotions (Algebra.TensorProduct.map (AlgHom.id O H) ga (d l)) = 0`. Rewrite using `[h0, map_zero]`.
-/
theorem exists_theta : ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] [Module.Free O H] (y : specO O H ⟶ G), y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ (ε : H →ₐ[O] O) (l : H) (c : O), ptMap ε ≫ y = 1 → (∀ h, ε h = 0 → h * l = 0) → ε l = c → l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) → ∃ Θ : H ⊗[O] H, (∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) ∧ Algebra.TensorProduct.lmul' O Θ = algebraMap O H c ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K], (∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0) → ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0 := by
  intro O _ _ G _ _ n H _ _ _ _ y hy hU ε l c hε hann hεl hlm
  have tors : ∀ (S : Type) [CommRing S] [Algebra O S] (f : specO O S ⟶ specO O H), (f ≫ y) ^ n = 1 := by
    intro S _ _ f
    rw [← comp_pow, hy, comp_one]
  have uniq : ∀ (S : Type) [CommRing S] [Algebra O S] (φ₁ φ₂ : H →ₐ[O] S),
      ptMap φ₁ ≫ y = ptMap φ₂ ≫ y → φ₁ = φ₂ := by
    intro S _ _ φ₁ φ₂ h
    obtain ⟨φ, -, hφ⟩ := hU S (ptMap φ₂ ≫ y) (tors S _)
    exact (hφ φ₁ h).trans (hφ φ₂ rfl).symm
  let iL : H →ₐ[O] H ⊗[O] H := Algebra.TensorProduct.includeLeft
  let iR : H →ₐ[O] H ⊗[O] H := Algebra.TensorProduct.includeRight
  obtain ⟨d, hd, -⟩ := hU (H ⊗[O] H) (ptMap iL ≫ y * (ptMap iR ≫ y)⁻¹)
    (by rw [mul_pow, inv_pow, tors, tors, inv_one, _root_.mul_one])
  obtain ⟨m, hm, -⟩ := hU (H ⊗[O] H) (ptMap iL ≫ y * ptMap iR ≫ y)
    (by rw [mul_pow, tors, tors, _root_.mul_one])
  let eH : H →ₐ[O] H := (Algebra.ofId O H).comp ε
  have heH : ptMap eH ≫ y = 1 := by
    rw [ptMap_comp_comp, hε, comp_one]

  have hmd : (Algebra.TensorProduct.lmul' O : H ⊗[O] H →ₐ[O] H).comp d = eH := by
    apply uniq
    rw [ptMap_comp_comp, hd, comp_mul, GrpObj.comp_inv, ← ptMap_comp_comp, ← ptMap_comp_comp, heH]
    have h1 : (Algebra.TensorProduct.lmul' O : H ⊗[O] H →ₐ[O] H).comp iL = AlgHom.id O H := by
      ext x; simp [iL]
    have h2 : (Algebra.TensorProduct.lmul' O : H ⊗[O] H →ₐ[O] H).comp iR = AlgHom.id O H := by
      ext x; simp [iR]
    rw [h1, h2, mul_inv_cancel]
  refine ⟨d l, ?_, ?_, ?_⟩
  ·
    have hl' : ∀ a : H, a * l = algebraMap O H (ε a) * l := by
      intro a
      have := hann (a - algebraMap O H (ε a)) (by simp)
      rwa [sub_mul, sub_eq_zero] at this
    let e2 : H ⊗[O] H →ₐ[O] H := Algebra.TensorProduct.lift eH (AlgHom.id O H) (fun _ _ => Commute.all _ _)
    have hkey : ∀ x : H ⊗[O] H, x * (l ⊗ₜ[O] (1 : H)) = (l ⊗ₜ[O] (1 : H)) * ((1 : H) ⊗ₜ[O] e2 x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [e2, eH, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
          _root_.one_mul, hl' a, AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.id_apply]
        rw [← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
      | add x x' hx hx' => rw [add_mul, hx, hx', map_add, TensorProduct.tmul_add, mul_add]
    let ψ : H ⊗[O] H →ₐ[O] H ⊗[O] H := Algebra.TensorProduct.lift d iR (fun _ _ => Commute.all _ _)
    have hψL : ψ.comp iL = d := by ext x; simp [ψ, iL]
    have hψR : ψ.comp iR = iR := by ext x; simp [ψ, iR]
    have he2L : e2.comp iL = eH := by ext x; simp [e2, iL]
    have he2R : e2.comp iR = AlgHom.id O H := by ext x; simp [e2, iR]
    have he2m : e2.comp m = AlgHom.id O H := by
      apply uniq
      rw [ptMap_comp_comp, hm, comp_mul, ← ptMap_comp_comp, ← ptMap_comp_comp, he2L, he2R, heH, _root_.one_mul]
    have hψm : ψ.comp m = iL := by
      apply uniq
      rw [ptMap_comp_comp, hm, comp_mul, ← ptMap_comp_comp, ← ptMap_comp_comp, hψL, hψR, hd,
        inv_mul_cancel_right]
    intro h
    have a1 : h ⊗ₜ[O] (1 : H) = ψ (m h) := by
      rw [← AlgHom.comp_apply, hψm]; rfl
    have a2 : d l = ψ (l ⊗ₜ[O] (1 : H)) := by simp [ψ]
    have a3 : (1 : H) ⊗ₜ[O] h = ψ ((1 : H) ⊗ₜ[O] h) := by simp [ψ, iR]
    have a4 : e2 (m h) = h := by rw [← AlgHom.comp_apply, he2m]; rfl
    rw [a1, a2, ← map_mul, hkey, a4, map_mul, ← a3, ← a2, _root_.mul_comm]
  · have := DFunLike.congr_fun hmd l
    rw [AlgHom.comp_apply] at this
    rw [this]
    simp [eH, hεl]
  · intro K _ _ _ _ ga
    let jL : H →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.includeLeft
    let jR : K →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.includeRight
    let κ : H ⊗[O] H →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.map (AlgHom.id O H) ga
    let Sg : H →ₐ[O] H ⊗[O] K := κ.comp m
    let MainNotions : H ⊗[O] K →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.lift Sg jR (fun _ _ => Commute.all _ _)
    have hκL : κ.comp iL = jL := by ext x; simp [κ, iL, jL]
    have hκR : κ.comp iR = jR.comp ga := by ext x; simp [κ, iR, jR]
    have hSL : (MainNotions.comp κ).comp iL = Sg := by ext x; simp [MainNotions, κ, iL]
    have hSR : (MainNotions.comp κ).comp iR = jR.comp ga := by ext x; simp [MainNotions, κ, iR, jR]
    have hSg : ptMap Sg ≫ y = ptMap jL ≫ y * ptMap (jR.comp ga) ≫ y := by
      rw [ptMap_comp_comp, hm, comp_mul, ← ptMap_comp_comp, ← ptMap_comp_comp, hκL, hκR]
    have hback : (MainNotions.comp κ).comp d = jL := by
      apply uniq
      rw [ptMap_comp_comp, hd, comp_mul, GrpObj.comp_inv, ← ptMap_comp_comp, ← ptMap_comp_comp, hSL, hSR, hSg,
        mul_inv_cancel_right]
    intro h0
    apply tmul_one_ne_zero l hlm K
    have := DFunLike.congr_fun hback l
    simp only [AlgHom.comp_apply] at this
    change MainNotions (κ (d l)) = l ⊗ₜ[O] (1 : K) at this
    rw [← this]
    change MainNotions (Algebra.TensorProduct.map (AlgHom.id O H) ga (d l)) = 0
    rw [h0, map_zero]

end GlobalTheory.TorsionTheta
