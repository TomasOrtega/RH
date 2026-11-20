import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SubsingletonOfLeOne

noncomputable section

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan.ConeSub

/- English proof (translation)
Establish `key : ∀ t : ℤ, 0 ≤ γ w w + 2 * t * γ u w`. Introduce `t`. Establish `h` using `hp (w + t • u)`. Simplify using `only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hu, hs w u] at h`. Combine the linear equalities and inequalities to obtain the conclusion.

Assume the negation of the conclusion as `h`. Establish `h1` using `key (-(γ w w + 1) * γ u w)`. Establish `h2 : 0 < γ u w * γ u w` using `mul_self_pos.2 h`. Establish `h3` using `hp w`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem eq_zero_of_self_eq_zero {X : Type} [AddCommGroup X] (γ : LinearMap.BilinForm ℤ X)
    (hs : ∀ y z, γ y z = γ z y) (hp : ∀ y, 0 ≤ γ y y) {u : X} (hu : γ u u = 0) (w : X) : γ u w = 0 := by
  have key : ∀ t : ℤ, 0 ≤ γ w w + 2 * t * γ u w := by
    intro t
    have h := hp (w + t • u)
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hu, hs w u] at h
    linarith
  by_contra h
  have h1 := key (-(γ w w + 1) * γ u w)
  have h2 : 0 < γ u w * γ u w := mul_self_pos.2 h
  have h3 := hp w
  nlinarith

/- English proof (translation)
Simplify using `only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring`.
-/
theorem sum_expand {X₁ ι : Type} [AddCommGroup X₁] [Fintype ι] (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (b : ι → X₁) (z : ι → ℤ) :
    ∑ k, ∑ l, (z k : ℝ) * z l * B (b k) (b l) = B (∑ k, z k • b k) (∑ l, z l • b l) := by
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/- English proof (translation)
Introduce `O _ _ _ _ bar X _ _ _ m γ c hbal hpsd hc`. Use `set S : Finset (Fin m) := Finset.univ.filter (fun i => 0 < c i) with hSdef`. Establish `hcS : ∀ i, i ∉ S → c i = 0` using `fun i hi => le_antisymm (not_lt.1 fun h => hi (by simp [hSdef, h])) (hc i)`. Distinguish the cases in `hS : S.Nonempty`. Use `swap`.

Establish `h0 : ∑ i, c i • toReal (γ i) = 0` using `Finset.sum_eq_zero fun i _ => by`. Rewrite using `[hcS i fun h => hS ⟨i, h⟩, zero_smul]`. Rewrite using `[h0]`. Conclude with `zero_mem_psdCone`. Use `set B := ∑ i, c i • toReal (γ i) with hBdef`.

Establish `hBapp : ∀ a b, B a b = ∑ i, c i * (γ i a b : ℝ)` using `fun a b => by`. Simplify using `[hBdef, LinearMap.sum_apply]`. Establish `hBreal : B ∈ realForms bar X` using `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (toReal_mem (hbal i))`. Set `R : Submodule O X` to `{ carrier := {y | ∀ i ∈ S, ∀ z, γ i y z = 0} add_mem' := fun {y y'} hy hy' i hi z => by rw [map_add, LinearMap.add_apply, hy i hi, hy' i hi, add_zero] zero_mem' := fun i _ z => by simp smul_mem' := fun a y hy i hi z => by`. Express the relevant statement in the definitionally equal form `γ i (a • y) z = 0`.

Rewrite using `[(hbal i).2 a y z]`. Conclude with `hy i hi _ }`. Establish `hmemR : ∀ y, y ∈ R ↔ ∀ i ∈ S, ∀ z, γ i y z = 0` using `fun y => Iff.rfl`. Establish `hBR1 : ∀ y ∈ R, ∀ z, B y z = 0` using `fun y hy z => by`. Rewrite using `[hBapp]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i ∈ S`. Rewrite using `[(hmemR y).1 hy i hi z]`. Simplify using the standard rewrite rules. Rewrite using `[hcS i hi, zero_mul]`.

Establish `hBsymm : ∀ y z, B y z = B z y` using `hBreal.1`. Establish `hBR2 : ∀ y ∈ R, ∀ z, B z y = 0` using `fun y hy z => by rw [hBsymm]; exact hBR1 y hy z`. Establish `hZ : ∀ n : ℤ, n ≠ 0 → ∀ y, n • y ∈ R → y ∈ R` using `fun n hn y hy i hi z => by`. Establish `h` using `(hmemR _).1 hy i hi z`. Rewrite `h` using `[map_zsmul, LinearMap.smul_apply, smul_eq_mul]`.

Conclude with `(mul_eq_zero.1 h).resolve_left hn`. Establish `hO : ∀ a : O, a ≠ 0 → ∀ y, a • y ∈ R → y ∈ R`. Introduce `a ha y hy`. Establish `hne : (Ideal.span {a}).comap (algebraMap ℤ O) ≠ ⊥` using `Ideal.comap_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)`. Take `⟨n, hn, hn0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`.

Take `⟨a', ha'⟩` from `Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hn)`. Use `hZ n hn0 y fun i hi z => ?_` and prove the remaining obligations. Establish `h` using `(hmemR _).1 hy i hi (bar a' • z)`. Rewrite `h` using `[← (hbal i).2 a' (a • y) z, smul_smul, ha', algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul]`. Conclude with `h`.

Establish `htor : Submodule.torsion O (X ⧸ R) = ⊥`. Use `(Submodule.eq_bot_iff _).2 fun u hu => ?_` and prove the remaining obligations. Take `⟨⟨a, ha⟩, hau⟩` from `(Submodule.mem_torsion_iff u).1 hu`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective R u`. Rewrite `hau` using `[Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`.

Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `hO a (nonZeroDivisors.ne_zero ha) y hau`. Establish `: Module.Flat O (X ⧸ R)` using `IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor`. Establish `: Module.FinitePresentation O (X ⧸ R)` using `Module.finitePresentation_of_finite _ _`. Establish `hproj : Module.Projective O (X ⧸ R)` using `Module.Flat.projective_of_finitePresentation`.

Establish `: Module.Finite ℤ (X ⧸ R)` using `Module.Finite.trans O (X ⧸ R)`. Establish `: IsAddTorsionFree (X ⧸ R)`. Use `⟨fun n hn a b hab => ?_⟩` and prove the remaining obligations. Proceed by induction on `a using Submodule.Quotient.induction_on with | H x => ?_`. Proceed by induction on `b using Submodule.Quotient.induction_on with | H y => ?_`.

Simplify using `only at hab`. Rewrite `hab` using `[← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]`. Rewrite using `[Submodule.Quotient.eq]`. Use `hZ n (by exact_mod_cast hn) (x - y) ?_` and prove the remaining obligations. Rewrite using `[natCast_zsmul, smul_sub]`.

Conclude with `hab`. Establish `: Module.Free ℤ (X ⧸ R)` using `Module.free_of_finite_type_torsion_free'`. Establish `hBq : ∀ x x' y y', Submodule.Quotient.mk (p` using `R) x = Submodule.Quotient.mk x' → Submodule.Quotient.mk (p := R) y = Submodule.Quotient.mk y' → B x y = B x' y' := by`. Introduce `x x' y y' hx hy`. Rewrite `hx`, `hy` using `[Submodule.Quotient.eq]`.

Establish `e1 : B x y = B (x - x') y + B x' (y - y') + B x' y'`. Simplify using `only [map_sub, LinearMap.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, hBR1 _ hx, hBR2 _ hy, zero_add, zero_add]`. Set `s` to `Function.surjInv (Submodule.Quotient.mk_surjective R)`.

Establish `hs : ∀ u, Submodule.Quotient.mk (p` using `R) (s u) = u := Function.surjInv_eq _`. Set `B₁` to `(AddMonoidHom.mk' (fun u => (AddMonoidHom.mk' (fun v => B (s u) (s v)) (fun v v' => by`. Rewrite using `[← map_add]; exact hBq _ _ _ _ rfl (by rw [hs, Submodule.Quotient.mk_add, hs, hs]))).toIntLinearMap)`. Use the proof step `(fun u u' => by`. Use extensionality with `v`.

Express the relevant statement in the definitionally equal form `B (s (u + u')) (s v) = B (s u) (s v) + B (s u') (s v)`. Rewrite using `[← LinearMap.add_apply, ← map_add]`. Conclude with `hBq _ _ _ _ (by rw [hs, Submodule.Quotient.mk_add, hs, hs]) rfl)).toIntLinearMap`. Establish `hB₁ : ∀ u v, B₁ u v = B (s u) (s v)` using `fun u v => rfl`. Establish `hBB₁ : ∀ a b, B a b = B₁ (Submodule.Quotient.mk a) (Submodule.Quotient.mk b)` using `fun a b => hBq _ _ _ _ (hs _).symm (hs _).symm`.

Establish `hreal₁ : B₁ ∈ realForms bar (X ⧸ R)`. Use `⟨fun u v => by rw [hB₁, hB₁, hBsymm], fun a u v => ?_⟩` and prove the remaining obligations. Rewrite using `[hB₁, hB₁]`. Combine the equalities or inequalities in the displayed calculation. Use `set cmin := S.inf' hS c with hcmin`.

Establish `hcmin0 : 0 < cmin` using `(Finset.lt_inf'_iff hS).2 fun i hi => (Finset.mem_filter.1 hi).2`. Establish `hint : ∀ u : X ⧸ R, u ≠ 0 → cmin ≤ B₁ u u`. Introduce `u hu`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi, hpos⟩ : ∃ i ∈ S, 0 < γ i (s u) (s u) := by`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Apply `hu` to reduce the goal to its premises. Rewrite using `[← hs u, Submodule.Quotient.mk_eq_zero]`. Conclude with `fun i hi z => eq_zero_of_self_eq_zero (γ i) (hbal i).1 (hpsd i) (le_antisymm (hne i hi) (hpsd i _)) z`. Rewrite using `[hB₁, hBapp]`.

Establish `h1 : (1 : ℝ) ≤ γ i (s u) (s u)` using `by exact_mod_cast hpos`. Combine the equalities or inequalities in the displayed calculation. Establish `hdef : IsPosDef B₁`. Set `b` to `Module.Free.chooseBasis ℤ (X ⧸ R)`. Rewrite using `[isPosDef_iff_basis b]`.

Introduce `x hx`. Use `GlobalTheory.PointLawsEdge.real_pos_of_int_ge (fun k l => B₁ (b k) (b l)) (fun k l => hreal₁.1 _ _) hcmin0 (fun z hz => ?_) x hx` and prove the remaining obligations. Use `show cmin ≤ ∑ k, ∑ l, (z k : ℝ) * z l * B₁ (b k) (b l)`. Rewrite using `[sum_expand]`. Use `hint _ fun h0 => hz ?_` and prove the remaining obligations.

Conclude with `funext (Fintype.linearIndependent_iff.1 b.linearIndependent z h0)`. Conclude with `⟨X ⧸ R, inferInstance, inferInstance, hproj, R.mkQ, B₁, Submodule.mkQ_surjective R, hreal₁, hdef, fun a b => hBB₁ a b⟩`.
-/
theorem sum_smul_toReal_mem_psdCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
    (∀ i, γ i ∈ balForms bar X) → (∀ i y, 0 ≤ γ i y y) → (∀ i, 0 ≤ c i) →
    ∑ i, c i • toReal (γ i) ∈ psdCone bar X := by
  intro O _ _ _ _ bar X _ _ _ m γ c hbal hpsd hc
  classical
  set S : Finset (Fin m) := Finset.univ.filter (fun i => 0 < c i) with hSdef
  have hcS : ∀ i, i ∉ S → c i = 0 := fun i hi =>
    le_antisymm (not_lt.1 fun h => hi (by simp [hSdef, h])) (hc i)
  by_cases hS : S.Nonempty
  swap
  · have h0 : ∑ i, c i • toReal (γ i) = 0 := Finset.sum_eq_zero fun i _ => by
      rw [hcS i fun h => hS ⟨i, h⟩, zero_smul]
    rw [h0]
    exact zero_mem_psdCone
  set B := ∑ i, c i • toReal (γ i) with hBdef
  have hBapp : ∀ a b, B a b = ∑ i, c i * (γ i a b : ℝ) := fun a b => by
    simp [hBdef, LinearMap.sum_apply]
  have hBreal : B ∈ realForms bar X :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (toReal_mem (hbal i))

  let R : Submodule O X :=
    { carrier := {y | ∀ i ∈ S, ∀ z, γ i y z = 0}
      add_mem' := fun {y y'} hy hy' i hi z => by rw [map_add, LinearMap.add_apply, hy i hi, hy' i hi, add_zero]
      zero_mem' := fun i _ z => by simp
      smul_mem' := fun a y hy i hi z => by
        change γ i (a • y) z = 0
        rw [(hbal i).2 a y z]; exact hy i hi _ }
  have hmemR : ∀ y, y ∈ R ↔ ∀ i ∈ S, ∀ z, γ i y z = 0 := fun y => Iff.rfl
  have hBR1 : ∀ y ∈ R, ∀ z, B y z = 0 := fun y hy z => by
    rw [hBapp]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ S
    · rw [(hmemR y).1 hy i hi z]; simp
    · rw [hcS i hi, zero_mul]
  have hBsymm : ∀ y z, B y z = B z y := hBreal.1
  have hBR2 : ∀ y ∈ R, ∀ z, B z y = 0 := fun y hy z => by rw [hBsymm]; exact hBR1 y hy z

  have hZ : ∀ n : ℤ, n ≠ 0 → ∀ y, n • y ∈ R → y ∈ R := fun n hn y hy i hi z => by
    have h := (hmemR _).1 hy i hi z
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left hn
  have hO : ∀ a : O, a ≠ 0 → ∀ y, a • y ∈ R → y ∈ R := by
    intro a ha y hy
    have hne : (Ideal.span {a}).comap (algebraMap ℤ O) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hn)
    refine hZ n hn0 y fun i hi z => ?_
    have h := (hmemR _).1 hy i hi (bar a' • z)
    rw [← (hbal i).2 a' (a • y) z, smul_smul, ha', algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul] at h
    exact h
  have htor : Submodule.torsion O (X ⧸ R) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    obtain ⟨⟨a, ha⟩, hau⟩ := (Submodule.mem_torsion_iff u).1 hu
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective R u
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hau
    rw [Submodule.Quotient.mk_eq_zero]
    exact hO a (nonZeroDivisors.ne_zero ha) y hau
  have : Module.Flat O (X ⧸ R) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  have : Module.FinitePresentation O (X ⧸ R) := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective O (X ⧸ R) := Module.Flat.projective_of_finitePresentation
  have : Module.Finite ℤ (X ⧸ R) := Module.Finite.trans O (X ⧸ R)
  have : IsAddTorsionFree (X ⧸ R) := by
    refine ⟨fun n hn a b hab => ?_⟩
    induction a using Submodule.Quotient.induction_on with | H x => ?_
    induction b using Submodule.Quotient.induction_on with | H y => ?_
    simp only at hab
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hab
    rw [Submodule.Quotient.eq]
    refine hZ n (by exact_mod_cast hn) (x - y) ?_
    rw [natCast_zsmul, smul_sub]; exact hab
  have : Module.Free ℤ (X ⧸ R) := Module.free_of_finite_type_torsion_free'

  have hBq : ∀ x x' y y', Submodule.Quotient.mk (p := R) x = Submodule.Quotient.mk x' →
      Submodule.Quotient.mk (p := R) y = Submodule.Quotient.mk y' → B x y = B x' y' := by
    intro x x' y y' hx hy
    rw [Submodule.Quotient.eq] at hx hy
    have e1 : B x y = B (x - x') y + B x' (y - y') + B x' y' := by
      simp only [map_sub, LinearMap.sub_apply]; ring
    rw [e1, hBR1 _ hx, hBR2 _ hy, zero_add, zero_add]
  let s := Function.surjInv (Submodule.Quotient.mk_surjective R)
  have hs : ∀ u, Submodule.Quotient.mk (p := R) (s u) = u := Function.surjInv_eq _
  let B₁ := (AddMonoidHom.mk' (fun u => (AddMonoidHom.mk' (fun v => B (s u) (s v)) (fun v v' => by
      rw [← map_add]; exact hBq _ _ _ _ rfl (by rw [hs, Submodule.Quotient.mk_add, hs, hs]))).toIntLinearMap)
    (fun u u' => by
      ext v
      change B (s (u + u')) (s v) = B (s u) (s v) + B (s u') (s v)
      rw [← LinearMap.add_apply, ← map_add]
      exact hBq _ _ _ _ (by rw [hs, Submodule.Quotient.mk_add, hs, hs]) rfl)).toIntLinearMap
  have hB₁ : ∀ u v, B₁ u v = B (s u) (s v) := fun u v => rfl
  have hBB₁ : ∀ a b, B a b = B₁ (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) := fun a b =>
    hBq _ _ _ _ (hs _).symm (hs _).symm
  have hreal₁ : B₁ ∈ realForms bar (X ⧸ R) := by
    refine ⟨fun u v => by rw [hB₁, hB₁, hBsymm], fun a u v => ?_⟩
    rw [hB₁, hB₁]
    calc B (s (a • u)) (s v) = B (a • s u) (s v) := hBq _ _ _ _ (by rw [hs, Submodule.Quotient.mk_smul, hs]) rfl
      _ = B (s u) (bar a • s v) := hBreal.2 a _ _
      _ = B (s u) (s (bar a • v)) := hBq _ _ _ _ rfl (by rw [hs, Submodule.Quotient.mk_smul, hs])
  set cmin := S.inf' hS c with hcmin
  have hcmin0 : 0 < cmin := (Finset.lt_inf'_iff hS).2 fun i hi => (Finset.mem_filter.1 hi).2
  have hint : ∀ u : X ⧸ R, u ≠ 0 → cmin ≤ B₁ u u := by
    intro u hu
    obtain ⟨i, hi, hpos⟩ : ∃ i ∈ S, 0 < γ i (s u) (s u) := by
      by_contra hne
      push_neg at hne
      apply hu
      rw [← hs u, Submodule.Quotient.mk_eq_zero]
      exact fun i hi z => eq_zero_of_self_eq_zero (γ i) (hbal i).1 (hpsd i)
        (le_antisymm (hne i hi) (hpsd i _)) z
    rw [hB₁, hBapp]
    have h1 : (1 : ℝ) ≤ γ i (s u) (s u) := by exact_mod_cast hpos
    calc cmin ≤ c i := Finset.inf'_le _ hi
      _ ≤ c i * (γ i (s u) (s u) : ℝ) := le_mul_of_one_le_right (hc i) h1
      _ ≤ ∑ j, c j * (γ j (s u) (s u) : ℝ) :=
        Finset.single_le_sum (f := fun j => c j * (γ j (s u) (s u) : ℝ))
          (fun j _ => mul_nonneg (hc j) (by exact_mod_cast hpsd j _)) (Finset.mem_univ i)
  have hdef : IsPosDef B₁ := by
    let b := Module.Free.chooseBasis ℤ (X ⧸ R)
    rw [isPosDef_iff_basis b]
    intro x hx
    refine GlobalTheory.PointLawsEdge.real_pos_of_int_ge (fun k l => B₁ (b k) (b l)) (fun k l => hreal₁.1 _ _) hcmin0
      (fun z hz => ?_) x hx
    show cmin ≤ ∑ k, ∑ l, (z k : ℝ) * z l * B₁ (b k) (b l)
    rw [sum_expand]
    refine hint _ fun h0 => hz ?_
    exact funext (Fintype.linearIndependent_iff.1 b.linearIndependent z h0)
  exact ⟨X ⧸ R, inferInstance, inferInstance, hproj, R.mkQ, B₁, Submodule.mkQ_surjective R, hreal₁, hdef,
    fun a b => hBB₁ a b⟩
