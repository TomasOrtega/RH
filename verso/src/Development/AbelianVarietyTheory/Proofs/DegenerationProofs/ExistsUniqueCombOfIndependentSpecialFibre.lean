import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SaturatedSections

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `t c h`. Conclude with `⟨c, fun i => by simp, fun j => by simpa using h j⟩`. Consider the case `succ n ih`.

Introduce `t c h`. Establish `hc` using `ind c (fun j => φ j (ϖ ^ n) * t j) (fun j => by`. Rewrite using `[← h j, pow_succ', map_mul, _root_.mul_assoc])`. Rewrite `hc` using `[hϖ.maximalIdeal_eq]`. Use `choose c' hc' using fun i => Ideal.mem_span_singleton'.1 (hc i)`.

Take `⟨d, hd, hd'⟩` from `ih t c' (fun j => by`. Rewrite using `[← sub_eq_zero]`. Apply `reg j` to reduce the goal to its premises. Rewrite using `[mul_sub, ← _root_.mul_assoc, ← map_mul, ← pow_succ', h j, Finset.mul_sum, sub_eq_zero]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← hc' i, map_mul]`. Use the proof step `ring)`. Conclude with `⟨d, fun i => by rw [← hc' i, hd i]; ring, hd'⟩`.
-/
theorem exists_comb {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    {J : Type} {A : J → Type} [∀ j, CommRing (A j)] (φ : ∀ j, W →+* A j) {ϖ : W}
    (hϖ : Irreducible ϖ) (reg : ∀ j (x : A j), φ j ϖ * x = 0 → x = 0)
    {r : ℕ} (s : Fin r → ∀ j, A j)
    (ind : ∀ (c : Fin r → W) (y : ∀ j, A j), (∀ j, φ j ϖ * y j = ∑ i, φ j (c i) * s i j) →
      ∀ i, c i ∈ IsLocalRing.maximalIdeal W) (n : ℕ) :
    ∀ (t : ∀ j, A j) (c : Fin r → W), (∀ j, φ j (ϖ ^ n) * t j = ∑ i, φ j (c i) * s i j) →
      ∃ d : Fin r → W, (∀ i, c i = ϖ ^ n * d i) ∧ ∀ j, t j = ∑ i, φ j (d i) * s i j := by
  induction n with
  | zero =>
    intro t c h
    exact ⟨c, fun i => by simp, fun j => by simpa using h j⟩
  | succ n ih =>
    intro t c h
    have hc := ind c (fun j => φ j (ϖ ^ n) * t j) (fun j => by
      rw [← h j, pow_succ', map_mul, _root_.mul_assoc])
    rw [hϖ.maximalIdeal_eq] at hc
    choose c' hc' using fun i => Ideal.mem_span_singleton'.1 (hc i)
    obtain ⟨d, hd, hd'⟩ := ih t c' (fun j => by
      rw [← sub_eq_zero]
      apply reg j
      rw [mul_sub, ← _root_.mul_assoc, ← map_mul, ← pow_succ', h j, Finset.mul_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hc' i, map_mul]; ring)
    exact ⟨d, fun i => by rw [← hc' i, hd i]; ring, hd'⟩

/- English proof (translation)
Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ`. Take `⟨d, -, hd⟩` from `exists_comb φ hϖ reg s ind n t (fun i => (u⁻¹ : Wˣ) * c i) (fun j => by`. Simplify using `only [map_mul, _root_.mul_assoc, ← Finset.mul_sum, ← h j]`. Rewrite using `[← _root_.mul_assoc (φ j (u⁻¹ : Wˣ)), ← map_mul, Units.inv_mul, map_one, _root_.one_mul])`. Use `⟨d, hd, fun d' hd' => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Rewrite using `[← sub_eq_zero]`. Assume the negation of the conclusion as `hne`. Take `⟨m, v, hv⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ`. Take `⟨e, he, -⟩` from `exists_comb φ hϖ reg s ind (m + 1) (fun _ => 0) (fun i => d' i - d i) (fun j => by`.

Simplify using `only [map_sub, sub_mul, Finset.sum_sub_distrib, ← hd j, ← hd' j, sub_self, MulZeroClass.mul_zero])`. Establish `h1 : ϖ ^ m * (v : W) = ϖ ^ m * (ϖ * e i)`. Use `he i` as an intermediate fact. Rewrite `this` using `[hv]`. Take the linear combination `this`.

Establish `h2` using `mul_left_cancel₀ (pow_ne_zero m hϖ.ne_zero) h1`. Conclude with `hϖ.not_isUnit (isUnit_of_mul_isUnit_left (h2 ▸ v.isUnit))`.
-/
theorem existsUnique_comb {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    {J : Type} {A : J → Type} [∀ j, CommRing (A j)] (φ : ∀ j, W →+* A j) {ϖ : W}
    (hϖ : Irreducible ϖ) (reg : ∀ j (x : A j), φ j ϖ * x = 0 → x = 0)
    {r : ℕ} (s : Fin r → ∀ j, A j)
    (ind : ∀ (c : Fin r → W) (y : ∀ j, A j), (∀ j, φ j ϖ * y j = ∑ i, φ j (c i) * s i j) →
      ∀ i, c i ∈ IsLocalRing.maximalIdeal W) (t : ∀ j, A j) (a : W) (c : Fin r → W) (ha : a ≠ 0)
    (h : ∀ j, φ j a * t j = ∑ i, φ j (c i) * s i j) :
    ∃! d : Fin r → W, ∀ j, t j = ∑ i, φ j (d i) * s i j := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨d, -, hd⟩ := exists_comb φ hϖ reg s ind n t (fun i => (u⁻¹ : Wˣ) * c i) (fun j => by
    simp only [map_mul, _root_.mul_assoc, ← Finset.mul_sum, ← h j]
    rw [← _root_.mul_assoc (φ j (u⁻¹ : Wˣ)), ← map_mul, Units.inv_mul, map_one,
      _root_.one_mul])
  refine ⟨d, hd, fun d' hd' => ?_⟩
  funext i
  rw [← sub_eq_zero]
  by_contra hne
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  obtain ⟨e, he, -⟩ := exists_comb φ hϖ reg s ind (m + 1) (fun _ => 0) (fun i => d' i - d i)
    (fun j => by
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib, ← hd j, ← hd' j, sub_self,
        MulZeroClass.mul_zero])
  have h1 : ϖ ^ m * (v : W) = ϖ ^ m * (ϖ * e i) := by
    have := he i
    rw [hv] at this
    linear_combination this
  have h2 := mul_left_cancel₀ (pow_ne_zero m hϖ.ne_zero) h1
  exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (h2 ▸ v.isUnit))

noncomputable def cst {W : Type} [CommRing W] {H : Scheme.{0}} (p : H ⟶ Sp W) (U : H.Opens) :
    W →+* Γ(H, U) :=
  (p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cst_eq {W : Type} [CommRing W] {H : Scheme.{0}} (p : H ⟶ Sp W) (U : H.Opens) (a : W) :
    Out.resTop U (Out.scal p a) = cst p U a := rfl

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Establish `hr' : (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom r ∈ nonZeroDivisors Γ(Sp W, ⊤)`. Set `e` to `(Scheme.ΓSpecIso (CommRingCat.of W)).symm.commRingCatIsoToRingEquiv`. Establish `: IsDomain Γ(Sp W, ⊤)` using `e.symm.toMulEquiv.isDomain`. Use `mem_nonZeroDivisors_of_ne_zero fun h0 => hr (e.injective ?_)` and prove the remaining obligations. Rewrite using `[map_zero]`.

Conclude with `h0`. Use `H.IsSheaf.section_ext fun x hx ↦ ?_` and prove the remaining obligations. Take `⟨_, ⟨V', hV', rfl⟩, hxV, hVV : V' ≤ V⟩` from `H.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen`. Use `⟨V', hVV, hxV, ?_⟩` and prove the remaining obligations. Establish `hf : (p.appLE ⊤ V' le_top).hom.Flat` using `p.flat_appLE (isAffineOpen_top _) hV' le_top`.

Use `letI := (p.appLE ⊤ V' le_top).hom.toAlgebra`. Establish `: Module.Flat Γ(Sp W, ⊤) Γ(H, V')` using `hf`. Apply `Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(H, V')) hr'` to reduce the goal to its premises. Establish `h'` using `congrArg (H.presheaf.map (homOfLE hVV).op) h`. Rewrite `h'` using `[map_mul, map_zero, cst, RingHom.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]`.

Simplify `h'` using `[Algebra.smul_def, RingHom.algebraMap_toAlgebra]`.
-/
theorem eq_zero_of_cst_mul {W : Type} [CommRing W] [IsDomain W] {H : Scheme.{0}} (p : H ⟶ Sp W)
    [Flat p] (V : H.Opens) {r : W} (hr : r ≠ 0) (a : Γ(H, V)) (h : cst p V r * a = 0) :
    a = 0 := by
  have hr' : (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom r ∈ nonZeroDivisors Γ(Sp W, ⊤) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of W)).symm.commRingCatIsoToRingEquiv
    have : IsDomain Γ(Sp W, ⊤) := e.symm.toMulEquiv.isDomain
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hr (e.injective ?_)
    rw [map_zero]; exact h0
  refine H.IsSheaf.section_ext fun x hx ↦ ?_
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV, hVV : V' ≤ V⟩ :=
    H.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  refine ⟨V', hVV, hxV, ?_⟩
  have hf : (p.appLE ⊤ V' le_top).hom.Flat := p.flat_appLE (isAffineOpen_top _) hV' le_top
  letI := (p.appLE ⊤ V' le_top).hom.toAlgebra
  have : Module.Flat Γ(Sp W, ⊤) Γ(H, V') := hf
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(H, V')) hr'
  have h' := congrArg (H.presheaf.map (homOfLE hVV).op) h
  rw [map_mul, map_zero, cst, RingHom.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_map] at h'
  simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h'

/- English proof (translation)
Rewrite using `[← cst_eq, Out.resTop, Scheme.basicOpen_res, Out.scal, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]`. Introduce and unpack `⟨-, h⟩`. Establish `h' : p x ∈ PrimeSpectrum.basicOpen r` using `h`. Rewrite `h'` using `[hx]`. Conclude with `h' hr`.
-/
theorem not_mem_basicOpen_cst {W : Type} [CommRing W] [IsLocalRing W] {H : Scheme.{0}}
    (p : H ⟶ Sp W) (V : H.Opens) {r : W} (hr : r ∈ IsLocalRing.maximalIdeal W) (x : H)
    (hx : p x = IsLocalRing.closedPoint W) : x ∉ H.basicOpen (cst p V r) := by
  rw [← cst_eq, Out.resTop, Scheme.basicOpen_res, Out.scal, ← Scheme.preimage_basicOpen_top,
    basicOpen_eq_of_affine]
  rintro ⟨-, h⟩
  have h' : p x ∈ PrimeSpectrum.basicOpen r := h
  rw [hx] at h'
  exact h' hr

end GlobalTheory.SaturatedSections

open GlobalTheory.SaturatedSections in

/- English proof (translation)
Introduce `W _ _ _ H p _ M _ r s ind t ⟨a, c, ha, h⟩`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible W`. Simplify using `only [cst_eq] at ind h ⊢`. Use `existsUnique_comb (A := fun j => Γ(H, M.U j)) (fun j => cst p (M.U j)) hϖ (fun j x hx => eq_zero_of_cst_mul p _ hϖ.ne_zero x hx) (fun i j => (s i).f j) (fun c y hy => ind c fun j x _ hx => ?_) t.f a c ha h` and prove the remaining obligations. Rewrite using `[← hy j, Scheme.basicOpen_mul]`.

Conclude with `fun h => not_mem_basicOpen_cst p _ hϖ.not_isUnit x hx h.1`.
-/
theorem GlobalTheory.existsUnique_comb_of_independent_special_fibre : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (H : Scheme.{0}) (p : H ⟶ Sp W) [Flat p] (M : LB H), M.IsLB → ∀ (r : ℕ) (s : Fin r → LB.Sec M), (∀ c : Fin r → W, (∀ (j : M.ι) (x : H), x ∈ M.U j → p x = IsLocalRing.closedPoint W → x ∉ H.basicOpen (∑ i, Out.resTop _ (Out.scal p (c i)) * (s i).f j)) → ∀ i, c i ∈ IsLocalRing.maximalIdeal W) → ∀ t : LB.Sec M, (∃ (a : W) (c : Fin r → W), a ≠ 0 ∧ ∀ j, Out.resTop _ (Out.scal p a) * t.f j = ∑ i, Out.resTop _ (Out.scal p (c i)) * (s i).f j) → ∃! c : Fin r → W, ∀ j, t.f j = ∑ i, Out.resTop _ (Out.scal p (c i)) * (s i).f j := by
  intro W _ _ _ H p _ M _ r s ind t ⟨a, c, ha, h⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  simp only [cst_eq] at ind h ⊢
  refine existsUnique_comb (A := fun j => Γ(H, M.U j)) (fun j => cst p (M.U j)) hϖ
    (fun j x hx => eq_zero_of_cst_mul p _ hϖ.ne_zero x hx) (fun i j => (s i).f j)
    (fun c y hy => ind c fun j x _ hx => ?_) t.f a c ha h
  rw [← hy j, Scheme.basicOpen_mul]
  exact fun h => not_mem_basicOpen_cst p _ hϖ.not_isUnit x hx h.1
