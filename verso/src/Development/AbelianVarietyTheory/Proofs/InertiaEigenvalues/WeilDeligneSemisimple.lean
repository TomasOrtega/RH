import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `hm' : (m : ℤ) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `hdeg : deg (σ * (frob h ^ m) ^ (-(deg σ / m))) = deg σ % m`. Rewrite using `[deg_mul, deg_zpow, deg_pow, deg_frob, Int.emod_def]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨τ, hτ⟩` from `exists_eq_zpow_mul (deg_frob (h := h)) (σ * (frob h ^ m) ^ (-(deg σ / m)))`.

Establish `hr0 : 0 ≤ deg σ % (m : ℤ)` using `Int.emod_nonneg _ hm'`. Establish `hr1 : deg σ % (m : ℤ) < m` using `Int.emod_lt_of_pos _ (by exact_mod_cast hm)`. Use `⟨(deg σ % m).toNat, τ, deg σ / m, by omega, ?_⟩` and prove the remaining obligations. Establish `hz : frob h ^ (deg σ % (m : ℤ)).toNat = frob h ^ (deg σ % (m : ℤ))`. Rewrite using `[← zpow_natCast, Int.toNat_of_nonneg hr0]`.

Rewrite using `[hz, ← hdeg, ← hτ, mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]`.
-/
theorem exists_frob_pow_mul_ineIncl_mul (m : ℕ) (hm : 0 < m) (σ : Weil h) :
    ∃ (r : ℕ) (τ : Ine (F := E) A) (q : ℤ), r < m ∧
      σ = frob h ^ r * ineIncl h τ * (frob h ^ m) ^ q := by
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdeg : deg (σ * (frob h ^ m) ^ (-(deg σ / m))) = deg σ % m := by
    rw [deg_mul, deg_zpow, deg_pow, deg_frob, Int.emod_def]
    ring
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) (σ * (frob h ^ m) ^ (-(deg σ / m)))
  have hr0 : 0 ≤ deg σ % (m : ℤ) := Int.emod_nonneg _ hm'
  have hr1 : deg σ % (m : ℤ) < m := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  refine ⟨(deg σ % m).toNat, τ, deg σ / m, by omega, ?_⟩
  have hz : frob h ^ (deg σ % (m : ℤ)).toNat = frob h ^ (deg σ % (m : ℤ)) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hr0]
  rw [hz, ← hdeg, ← hτ, mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]

/- English proof (translation)
Take `⟨m, hm⟩ : ∃ m : ℕ, 0 < m` from `⟨1, one_pos⟩`. Use `⟨fun P => ?_⟩` and prove the remaining obligations. Establish `hPinv : P.toSubmodule ∈ Module.End.invtSubmodule (ρ (frob h ^ m))`. Rewrite using `[Module.End.mem_invtSubmodule]`. Introduce `v hv`.

Conclude with `P.apply_mem_toSubmodule _ hv`. Take `⟨Q, hQ, hc⟩` from `(Module.End.isSemisimple_iff.mp (hss (frob h ^ m))) _ hPinv`. Rewrite `hQ` using `[Module.End.mem_invtSubmodule]`. Set `p : Module.End ℂ V` to `P.toSubmodule.projection Q hc`. Establish `hp1 : ∀ v ∈ P.toSubmodule, p v = v` using `fun v hv => Submodule.projection_apply_left hc ⟨v, hv⟩`.

Establish `hp2 : ∀ v ∈ Q, p v = 0` using `fun v hv => Submodule.projection_apply_right hc ⟨v, hv⟩`. Establish `hpm : ∀ v, p v ∈ P.toSubmodule` using `fun v => Submodule.projection_apply_mem hc v`. Establish `hpT : ρ (frob h ^ m) * p = p * ρ (frob h ^ m)`. Use extensionality with `v`. Take `⟨x, hx, y, hy, rfl⟩` from `Submodule.mem_sup.1 (show v ∈ P.toSubmodule ⊔ Q by rw [hc.sup_eq_top]; trivial)`.

Simplify using `only [Module.End.mul_apply, map_add, hp1 _ hx, hp2 _ hy, add_zero, hp1 _ (hPinv hx), hp2 _ (hQ hy), map_zero]`. Establish `hinv : ∀ σ : Weil h, ρ σ * ρ σ⁻¹ = 1` using `fun σ => by rw [← map_mul, mul_inv_cancel, map_one]`. Establish `hinv' : ∀ σ : Weil h, ρ σ⁻¹ * ρ σ = 1` using `fun σ => by rw [← map_mul, inv_mul_cancel, map_one]`. Set `c : Weil h → Module.End ℂ V` to `fun σ => ρ σ * p * ρ σ⁻¹`. Establish `hcm : ∀ σ v, c σ v ∈ P.toSubmodule` using `fun σ v => P.apply_mem_toSubmodule σ (hpm _)`.

Establish `hc1 : ∀ σ, ∀ v ∈ P.toSubmodule, c σ v = v`. Introduce `σ v hv`. Use `show ρ σ (p (ρ σ⁻¹ v)) = v`. Rewrite using `[hp1 _ (P.apply_mem_toSubmodule _ hv), ← Module.End.mul_apply, hinv, Module.End.one_apply]`. Establish `hper : ∀ σ, c (σ * frob h ^ m) = c σ`.

Introduce `σ`. Simplify using `only [c, _root_.mul_inv_rev, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hzper : ∀ σ (q : ℤ), c (σ * (frob h ^ m) ^ q) = c σ`. Introduce `σ q`.

Proceed by induction on `q using Int.induction_on with`. Consider the case `zero => simp`. Consider the case `succ q ih => rw [_root_.zpow_add_one, ← mul_assoc, hper, ih]`. Consider the case `pred q ih`. Rewrite using `[← ih, ← hper, mul_assoc, ← _root_.zpow_add_one]`.

Use `congr 3`. Expand and normalize the polynomial expressions, which then agree. Establish `hFfin` using `hρ.finite_range`. Establish `hCfin : (Set.range c).Finite`. Use `(((Set.finite_Iio m).prod (hFfin.prod hFfin)).image (fun t : ℕ × (Module.End ℂ V × Module.End ℂ V) => ρ (frob h ^ t.1) * (t.2.1 * p * t.2.2) * ρ ((frob h ^ t.1)⁻¹))).subset ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨σ, rfl⟩`. Take `⟨r, τ, q, hr, rfl⟩` from `exists_frob_pow_mul_ineIncl_mul m hm σ`. Use `⟨(r, ρ (ineIncl h τ), ρ (ineIncl h τ⁻¹)), ⟨hr, ⟨τ, rfl⟩, ⟨τ⁻¹, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Use `show _ = c _`. Rewrite using `[hzper]`.

Simplify using `only [c, _root_.mul_inv_rev, map_mul, map_inv, mul_assoc]`. Use `set Cf := hCfin.toFinset with hCf`. Establish `hCmem : ∀ x, x ∈ Cf ↔ ∃ σ, c σ = x` using `fun x => by simp [Cf]`. Establish `hcard : Cf.card ≠ 0` using `Finset.card_ne_zero_of_mem ((hCmem _).2 ⟨1, rfl⟩)`. Set `S : Module.End ℂ V` to `∑ x ∈ Cf, x`.

Set `qa : Module.End ℂ V` to `(Cf.card : ℂ)⁻¹ • S`. Establish `hSm : ∀ v, S v ∈ P.toSubmodule`. Introduce `v`. Simplify using `only [S]`. Rewrite using `[LinearMap.sum_apply]`.

Use `P.toSubmodule.sum_mem fun x hx => ?_` and prove the remaining obligations. Take `⟨σ, rfl⟩` from `(hCmem x).1 hx`. Conclude with `hcm σ v`. Establish `hS1 : ∀ v ∈ P.toSubmodule, S v = (Cf.card : ℂ) • v`. Introduce `v hv`.

Simplify using `only [S]`. Rewrite using `[LinearMap.sum_apply]`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => v), Finset.sum_const, Nat.cast_smul_eq_nsmul]`. Introduce `x hx`. Take `⟨σ, rfl⟩` from `(hCmem x).1 hx`.

Conclude with `hc1 σ v hv`. Establish `hSeq : ∀ g : Weil h, ρ g * S = S * ρ g`. Introduce `g`. Establish `h1 : ∑ x ∈ Cf, ρ g * x * ρ g⁻¹ = ∑ x ∈ Cf, x`. Use `Finset.sum_nbij' (fun x => ρ g * x * ρ g⁻¹) (fun x => ρ g⁻¹ * x * ρ g) ?_ ?_ ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations.

Introduce `x hx`. Take `⟨σ, rfl⟩` from `(hCmem x).1 (Finset.mem_coe.1 hx)`. Conclude with `Finset.mem_coe.2 ((hCmem _).2 ⟨g * σ, by simp only [c, _root_.mul_inv_rev, map_mul, mul_assoc]⟩)`. Introduce `x hx`. Take `⟨σ, rfl⟩` from `(hCmem x).1 (Finset.mem_coe.1 hx)`.

Conclude with `Finset.mem_coe.2 ((hCmem _).2 ⟨g⁻¹ * σ, by`. Simplify using `only [c, _root_.mul_inv_rev, map_mul, inv_inv, mul_assoc]⟩)`. Introduce `x _`. Simplify using `only [← mul_assoc, hinv', one_mul]`. Rewrite using `[mul_assoc, hinv', mul_one]`.

Introduce `x _`. Simplify using `only [← mul_assoc, hinv, one_mul]`. Rewrite using `[mul_assoc, hinv, mul_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul]`.

Simplify using `only [S, Finset.mul_sum, mul_assoc, hinv', mul_one]`. Use `_ = S * ρ g := by rw [h1]`. Establish `hqm : ∀ v, qa v ∈ P.toSubmodule` using `fun v => P.toSubmodule.smul_mem _ (hSm v)`. Establish `hq1 : ∀ v ∈ P.toSubmodule, qa v = v`. Introduce `v hv`.

Use `show (Cf.card : ℂ)⁻¹ • S v = v`. Rewrite using `[hS1 v hv, inv_smul_smul₀ (by exact_mod_cast hcard)]`. Establish `hqe : ∀ g v, qa (ρ g v) = ρ g (qa v)`. Introduce `g v`. Use `show (Cf.card : ℂ)⁻¹ • S (ρ g v) = ρ g ((Cf.card : ℂ)⁻¹ • S v)`.

Rewrite using `[map_smul, ← Module.End.mul_apply S, ← hSeq, Module.End.mul_apply]`. Set `q' : V →ₗ[ℂ] P.toSubmodule` to `qa.codRestrict P.toSubmodule hqm`. Establish `hcompl : IsCompl P.toSubmodule (LinearMap.ker q')` using `LinearMap.isCompl_of_proj fun x => Subtype.ext (hq1 x x.2)`. Use `⟨⟨LinearMap.ker q', fun g v hv => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h0 : qa v = 0` using `congrArg Subtype.val hv`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show qa (ρ g v) = 0`. Rewrite using `[hqe, h0, map_zero]`. Rewrite using `[isCompl_iff, disjoint_iff, codisjoint_iff, ← Subrepresentation.toSubmodule_injective.eq_iff, ← Subrepresentation.toSubmodule_injective.eq_iff]`. Rewrite `hcompl` using `[isCompl_iff, disjoint_iff, codisjoint_iff]`.

Conclude with `hcompl`.
-/
theorem isSemisimpleRepresentation_of_isSmooth [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ)
    (hss : ∀ σ, Module.End.IsSemisimple (ρ σ)) : ρ.IsSemisimpleRepresentation := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 0 < m := ⟨1, one_pos⟩
  refine ⟨fun P => ?_⟩
  have hPinv : P.toSubmodule ∈ Module.End.invtSubmodule (ρ (frob h ^ m)) := by
    rw [Module.End.mem_invtSubmodule]
    intro v hv
    exact P.apply_mem_toSubmodule _ hv
  obtain ⟨Q, hQ, hc⟩ := (Module.End.isSemisimple_iff.mp (hss (frob h ^ m))) _ hPinv
  rw [Module.End.mem_invtSubmodule] at hQ
  let p : Module.End ℂ V := P.toSubmodule.projection Q hc
  have hp1 : ∀ v ∈ P.toSubmodule, p v = v := fun v hv => Submodule.projection_apply_left hc ⟨v, hv⟩
  have hp2 : ∀ v ∈ Q, p v = 0 := fun v hv => Submodule.projection_apply_right hc ⟨v, hv⟩
  have hpm : ∀ v, p v ∈ P.toSubmodule := fun v => Submodule.projection_apply_mem hc v
  have hpT : ρ (frob h ^ m) * p = p * ρ (frob h ^ m) := by
    ext v
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      Submodule.mem_sup.1 (show v ∈ P.toSubmodule ⊔ Q by rw [hc.sup_eq_top]; trivial)
    simp only [Module.End.mul_apply, map_add, hp1 _ hx, hp2 _ hy, add_zero,
      hp1 _ (hPinv hx), hp2 _ (hQ hy), map_zero]
  have hinv : ∀ σ : Weil h, ρ σ * ρ σ⁻¹ = 1 := fun σ => by rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : ∀ σ : Weil h, ρ σ⁻¹ * ρ σ = 1 := fun σ => by rw [← map_mul, inv_mul_cancel, map_one]
  let c : Weil h → Module.End ℂ V := fun σ => ρ σ * p * ρ σ⁻¹
  have hcm : ∀ σ v, c σ v ∈ P.toSubmodule := fun σ v => P.apply_mem_toSubmodule σ (hpm _)
  have hc1 : ∀ σ, ∀ v ∈ P.toSubmodule, c σ v = v := by
    intro σ v hv
    show ρ σ (p (ρ σ⁻¹ v)) = v
    rw [hp1 _ (P.apply_mem_toSubmodule _ hv), ← Module.End.mul_apply, hinv, Module.End.one_apply]
  have hper : ∀ σ, c (σ * frob h ^ m) = c σ := by
    intro σ
    simp only [c, _root_.mul_inv_rev, map_mul]
    calc ρ σ * ρ (frob h ^ m) * p * (ρ (frob h ^ m)⁻¹ * ρ σ⁻¹)
        = ρ σ * (ρ (frob h ^ m) * p * ρ (frob h ^ m)⁻¹) * ρ σ⁻¹ := by simp only [mul_assoc]
      _ = ρ σ * (p * (ρ (frob h ^ m) * ρ (frob h ^ m)⁻¹)) * ρ σ⁻¹ := by rw [hpT]; simp only [mul_assoc]
      _ = ρ σ * p * ρ σ⁻¹ := by rw [hinv, mul_one]
  have hzper : ∀ σ (q : ℤ), c (σ * (frob h ^ m) ^ q) = c σ := by
    intro σ q
    induction q using Int.induction_on with
    | zero => simp
    | succ q ih => rw [_root_.zpow_add_one, ← mul_assoc, hper, ih]
    | pred q ih =>
      rw [← ih, ← hper, mul_assoc, ← _root_.zpow_add_one]
      congr 3
      ring
  have hFfin := hρ.finite_range
  have hCfin : (Set.range c).Finite := by
    refine (((Set.finite_Iio m).prod (hFfin.prod hFfin)).image
      (fun t : ℕ × (Module.End ℂ V × Module.End ℂ V) =>
        ρ (frob h ^ t.1) * (t.2.1 * p * t.2.2) * ρ ((frob h ^ t.1)⁻¹))).subset ?_
    rintro _ ⟨σ, rfl⟩
    obtain ⟨r, τ, q, hr, rfl⟩ := exists_frob_pow_mul_ineIncl_mul m hm σ
    refine ⟨(r, ρ (ineIncl h τ), ρ (ineIncl h τ⁻¹)), ⟨hr, ⟨τ, rfl⟩, ⟨τ⁻¹, rfl⟩⟩, ?_⟩
    show _ = c _
    rw [hzper]
    simp only [c, _root_.mul_inv_rev, map_mul, map_inv, mul_assoc]
  set Cf := hCfin.toFinset with hCf
  have hCmem : ∀ x, x ∈ Cf ↔ ∃ σ, c σ = x := fun x => by simp [Cf]
  have hcard : Cf.card ≠ 0 := Finset.card_ne_zero_of_mem ((hCmem _).2 ⟨1, rfl⟩)
  let S : Module.End ℂ V := ∑ x ∈ Cf, x
  let qa : Module.End ℂ V := (Cf.card : ℂ)⁻¹ • S
  have hSm : ∀ v, S v ∈ P.toSubmodule := by
    intro v
    simp only [S]
    rw [LinearMap.sum_apply]
    refine P.toSubmodule.sum_mem fun x hx => ?_
    obtain ⟨σ, rfl⟩ := (hCmem x).1 hx
    exact hcm σ v
  have hS1 : ∀ v ∈ P.toSubmodule, S v = (Cf.card : ℂ) • v := by
    intro v hv
    simp only [S]
    rw [LinearMap.sum_apply]
    rw [Finset.sum_congr rfl (g := fun _ => v), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro x hx
    obtain ⟨σ, rfl⟩ := (hCmem x).1 hx
    exact hc1 σ v hv
  have hSeq : ∀ g : Weil h, ρ g * S = S * ρ g := by
    intro g
    have h1 : ∑ x ∈ Cf, ρ g * x * ρ g⁻¹ = ∑ x ∈ Cf, x := by
      refine Finset.sum_nbij' (fun x => ρ g * x * ρ g⁻¹) (fun x => ρ g⁻¹ * x * ρ g)
        ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · intro x hx
        obtain ⟨σ, rfl⟩ := (hCmem x).1 (Finset.mem_coe.1 hx)
        exact Finset.mem_coe.2 ((hCmem _).2 ⟨g * σ, by simp only [c, _root_.mul_inv_rev, map_mul, mul_assoc]⟩)
      · intro x hx
        obtain ⟨σ, rfl⟩ := (hCmem x).1 (Finset.mem_coe.1 hx)
        exact Finset.mem_coe.2 ((hCmem _).2 ⟨g⁻¹ * σ, by
          simp only [c, _root_.mul_inv_rev, map_mul, inv_inv, mul_assoc]⟩)
      · intro x _
        simp only [← mul_assoc, hinv', one_mul]
        rw [mul_assoc, hinv', mul_one]
      · intro x _
        simp only [← mul_assoc, hinv, one_mul]
        rw [mul_assoc, hinv, mul_one]
    calc ρ g * S = (∑ x ∈ Cf, ρ g * x * ρ g⁻¹) * ρ g := by
          rw [Finset.sum_mul]
          simp only [S, Finset.mul_sum, mul_assoc, hinv', mul_one]
      _ = S * ρ g := by rw [h1]
  have hqm : ∀ v, qa v ∈ P.toSubmodule := fun v => P.toSubmodule.smul_mem _ (hSm v)
  have hq1 : ∀ v ∈ P.toSubmodule, qa v = v := by
    intro v hv
    show (Cf.card : ℂ)⁻¹ • S v = v
    rw [hS1 v hv, inv_smul_smul₀ (by exact_mod_cast hcard)]
  have hqe : ∀ g v, qa (ρ g v) = ρ g (qa v) := by
    intro g v
    show (Cf.card : ℂ)⁻¹ • S (ρ g v) = ρ g ((Cf.card : ℂ)⁻¹ • S v)
    rw [map_smul, ← Module.End.mul_apply S, ← hSeq, Module.End.mul_apply]
  let q' : V →ₗ[ℂ] P.toSubmodule := qa.codRestrict P.toSubmodule hqm
  have hcompl : IsCompl P.toSubmodule (LinearMap.ker q') :=
    LinearMap.isCompl_of_proj fun x => Subtype.ext (hq1 x x.2)
  refine ⟨⟨LinearMap.ker q', fun g v hv => ?_⟩, ?_⟩
  · have h0 : qa v = 0 := congrArg Subtype.val hv
    apply Subtype.ext
    show qa (ρ g v) = 0
    rw [hqe, h0, map_zero]
  · rw [isCompl_iff, disjoint_iff, codisjoint_iff,
      ← Subrepresentation.toSubmodule_injective.eq_iff,
      ← Subrepresentation.toSubmodule_injective.eq_iff]
    rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hcompl
    exact hcompl

end GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.WDRep

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h n a`. Conclude with `isSemisimpleRepresentation_of_isSmooth a.ρ a.smooth a.semisimple`.
-/
theorem isSemisimpleRepresentation_rho : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (n : ℕ) (a : WDRep h (Fin n → ℂ)), a.ρ.IsSemisimpleRepresentation := by
  intro E Ω _ _ _ _ _ A w h n a
  exact isSemisimpleRepresentation_of_isSmooth a.ρ a.smooth a.semisimple

end GlobalTheory.WeilDeligne.WDRep
