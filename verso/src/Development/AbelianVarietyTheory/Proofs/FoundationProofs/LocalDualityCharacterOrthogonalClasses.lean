import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLePowIffDvdStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfUniformLimitCoboundariesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAnnihilatorDepthOfNotCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitCharacterOfIntegralCyclotomicProductStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfOrthogonalDualCharacterModPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulScalarClassEqSmulAddCoboundaryModPrimePStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

/- English proof (translation)
Introduce `hL l _ Ω _ _ _ c A k k' a b hA hk hk' ha hb hint hmul hk1 hk'1 hcob`. Distinguish the cases in `hac : ∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, a s = k' s * x - x`. Conclude with `Or.inr hac`. Use `left`. Take `⟨θ, hθc, hθ⟩` from `GlobalTheory.T.exists_unitCharacter_of_integral_cyclotomic_product l Ω c A k k' hk (fun s hs => ⟨(hint s hs).1, (hint s hs).2.1, (hint s hs).2.2.2.2⟩) (fun s hs t ht => (hmul s hs t ht).1)`.

Take `⟨θ', hθ'c, hθ'⟩` from `GlobalTheory.T.exists_unitCharacter_of_integral_cyclotomic_product l Ω c A k' k hk' (fun s hs => ⟨(hint s hs).2.1, (hint s hs).1, by rw [mul_comm]; exact (hint s hs).2.2.2.2⟩) (fun s hs t ht => (hmul s hs t ht).2.1)`. Establish `hN` using `GlobalTheory.T.norm_le_pow_iff_dvd l c`. Establish `hchi : ∀ s : G ℚ Ω, ((((UpperTheory.V.Base.chiO ℚ Ω l c.O) s : c.Oˣ) : c.O) : Qbar l) = eps l s`. Introduce `s`. Both sides reduce to the same expression.

Establish `hcyc : θ * θ' = (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F` using `ℚ) A).subtype := by`. Use `MonoidHom.ext fun g => Units.ext (Subtype.ext ?_)` and prove the remaining obligations. Simplify using `only [MonoidHom.mul_apply, Units.val_mul, Subalgebra.coe_mul, hθ, hθ', MonoidHom.comp_apply, Subgroup.coe_subtype, hchi]`. Conclude with `(hint g g.2).2.2.2.2`. Establish `hθ1 : ∃ g, θ g ≠ 1`.

Take `⟨s, hs, hne⟩` from `hk1`. Conclude with `⟨⟨s, hs⟩, fun h => hne (by have e := hθ ⟨s, hs⟩; rw [h] at e; exact e.symm.trans rfl)⟩`. Establish `hθ'1 : ∃ g, θ' g ≠ 1`. Take `⟨s, hs, hne⟩` from `hk'1`. Conclude with `⟨⟨s, hs⟩, fun h => hne (by have e := hθ' ⟨s, hs⟩; rw [h] at e; exact e.symm.trans rfl)⟩`.

Establish `hθ'ne : ∃ g, θ' g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F` using `ℚ) A).subtype g := by`. Take `⟨s, hs, hne⟩` from `hk1`. Use `⟨⟨s, hs⟩, fun h => hne ?_⟩` and prove the remaining obligations. Establish `e` using `DFunLike.congr_fun hcyc ⟨s, hs⟩`. Rewrite `e` using `[MonoidHom.mul_apply, ← h]`.

Establish `e1 : θ ⟨s, hs⟩ = 1` using `mul_eq_right.1 e`. Establish `e2` using `hθ ⟨s, hs⟩`. Rewrite `e2` using `[e1]`. Conclude with `e2.symm.trans rfl`. Use `set p : c.O := ((l : ℕ) : c.O) with hp`.

Set `aO : ↥(Dec (F` to `ℚ) A) → c.O := fun s => ⟨a s, (hint s.1 s.2).2.2.1⟩`. Set `bO : ↥(Dec (F` to `ℚ) A) → c.O := fun s => ⟨b s, (hint s.1 s.2).2.2.2.1⟩`. Establish `haO : Continuous aO` using `(continuousOn_iff_continuous_domRestrict.1 ha).subtype_mk _`. Establish `hbO : Continuous bO` using `(continuousOn_iff_continuous_domRestrict.1 hb).subtype_mk _`. Establish `haOc : ∀ s t, aO (s * t) = aO s + ((θ' s : c.Oˣ) : c.O) * aO t` using `fun s t => Subtype.ext (by`.

Simplify using `only [aO, Subalgebra.coe_add, Subalgebra.coe_mul, hθ']`. Conclude with `(hmul s.1 s.2 t.1 t.2).2.2.2)`. Establish `hbOc : ∀ s t, bO (s * t) = bO s + ((θ s : c.Oˣ) : c.O) * bO t` using `fun s t => Subtype.ext (by`. Simplify using `only [bO, Subalgebra.coe_add, Subalgebra.coe_mul, hθ]`. Conclude with `(hmul s.1 s.2 t.1 t.2).2.2.1)`.

Establish `hnorm1 : ∀ x : c.O, ‖((x : c.O) : Qbar l)‖ ≤ 1` using `fun x => by`. Use `(hN 0 x).2 (by simp); simpa using this` as an intermediate fact. Take `⟨r, hr⟩` from `GlobalTheory.T.exists_annihilatorDepth_of_not_coboundary l (Set.univ : Set ↥(Dec (F := ℚ) A)) (fun s => k' s) (fun s => a s) (by obtain ⟨s, hs, hne⟩ := hk'1; exact ⟨⟨s, hs⟩, trivial, hne⟩) (fun ⟨X, hX⟩ => hac ⟨X, fun s hs => hX ⟨s, hs⟩ trivial⟩)`. Establish `hann : ∀ n : ℕ, ∀ x y : c.O, (∀ s, p ^ n ∣ x * aO s - (((θ' s : c.Oˣ) : c.O) * y - y)) → p ^ (n - r) ∣ x`. Introduce `n x y h`.

Use `(hN (n - r) x).1 (hr n x y (hnorm1 x) fun s _ => ?_)` and prove the remaining obligations. Use `(hN n _).2 (h s)` as an intermediate fact. Simplify `this` using `[aO, hθ']`. Take `⟨m, hm0, hAF⟩` from `GlobalTheory.T.exists_mul_scalarClass_eq_smul_add_coboundary_modPrimePow hL.lf hL.lt hL.le l Ω c A hA θ' hθ'c hθ'1 hθ'ne r`. Establish `key : ∀ n : ℕ, 1 ≤ n → ∃ x : c.O, ∀ s, p ^ n ∣ (m : c.O) * bO s - (((θ s : c.Oˣ) : c.O) * x - x)`.

Introduce `n hn`. Use `GlobalTheory.T.coboundary_of_orthogonal_dualCharacter_modPrimePow hL.lf hL.lt l Ω c A hA θ θ' hθc hθ'c hcyc n hn (fun s => (m : c.O) * bO s) (continuous_const.mul hbO) (fun s t => ?_) (fun a' ha' hca' => ?_)` and prove the remaining obligations. Rewrite using `[hbOc s t]`. Put the polynomial expressions in normal form. Conclude with `dvd_zero _`.

Take `⟨x, y, hxy⟩` from `hAF n hn aO haO (fun s t => by rw [haOc s t, sub_self]; exact dvd_zero _) (hann n) a' ha' hca'`. Take `⟨u, huc, huO, hu⟩` from `hcob n`. Set `u0 : ↥(Dec (F` to `ℚ) A) → c.O := fun s => ⟨u s, huO s⟩`. Establish `hu0c : Continuous u0` using `(continuousOn_iff_continuous_domRestrict.1 huc).subtype_mk _`. Establish `hu0 : ∀ s t, p ^ n ∣ bO s * (((θ' s : c.Oˣ) : c.O) * aO t) - ((((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O)) * u0 t - u0 (s * t) + u0 s)`.

Introduce `s t`. Use `(hN n _).1 ?_` and prove the remaining obligations. Establish `e : ‖b s.1 * (k' s.1 * a t.1) - (eps l s.1 * u t.1 - u (s.1 * t.1) + u s.1)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖` using `hu s.1 s.2 t.1 t.2`. Establish `he : k s.1 * k' s.1 = eps l s.1` using `(hint s.1 s.2).2.2.2.2`. Rewrite `e` using `[← he]`.

Use `e using 2` and compare the differences between its conclusion and the goal. Simplify using `only [aO, bO, u0, Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul, hθ, hθ']`. Both sides reduce to the same expression. Establish `hbt : Continuous (fun s => bO s * ((θ' s : c.Oˣ) : c.O))` using `hbO.mul hθ'c`. Establish `hcu : Continuous (fun s => x * u0 s - bO s * ((θ' s : c.Oˣ) : c.O) * y)` using `(continuous_const.mul hu0c).sub (hbt.mul continuous_const)`.

Use `⟨fun s => x * u0 s - bO s * ((θ' s : c.Oˣ) : c.O) * y, hcu, fun s t => ?_⟩` and prove the remaining obligations. Take `⟨q1, hq1⟩` from `hxy t`. Take `⟨q2, hq2⟩` from `hu0 s t`. Use `⟨bO s * ((θ' s : c.Oˣ) : c.O) * q1 + x * q2, ?_⟩` and prove the remaining obligations. Simplify using `only []`.

Rewrite using `[hbOc s t, map_mul θ' s t, Units.val_mul]`. Take the linear combination `(bO s * ((θ' s : c.Oˣ) : c.O)) * hq1 + x * hq2`. Take `⟨s0, hs0, hne0⟩` from `hk1`. Use `GlobalTheory.T.coboundary_of_uniform_limit_coboundaries (Dec (F := ℚ) A : Set (G ℚ Ω)) k b ⟨s0, hs0, hne0⟩ fun ε hε => ?_` and prove the remaining obligations. Establish `hl1 : ‖((l : ℕ) : Qbar l)‖ < 1`.

Establish `e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l])` using `by simp`. Rewrite using `[e, norm_algebraMap', Padic.norm_p]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)`. Establish `hm : (0 : ℝ) < ‖((m : ℕ) : Qbar l)‖` using `norm_pos_iff.2 (Nat.cast_ne_zero.2 hm0.ne')`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one (mul_pos hε hm) hl1`.

Take `⟨x, hx⟩` from `key (n + 1) (Nat.le_add_left 1 n)`. Use `⟨(x : Qbar l) / (m : Qbar l), fun s hs => ?_⟩` and prove the remaining obligations. Establish `e` using `(hN (n + 1) _).2 (hx ⟨s, hs⟩)`. Establish `e2 : ((((m : c.O) * bO ⟨s, hs⟩ - (((θ ⟨s, hs⟩ : c.Oˣ) : c.O) * x - x) : c.O)) : Qbar l) = (m : Qbar l) * (b s - (k s * ((x : Qbar l) / (m : Qbar l)) - (x : Qbar l) / (m : Qbar l)))`. Establish `hm' : (m : Qbar l) ≠ 0` using `Nat.cast_ne_zero.2 hm0.ne'`.

Establish `hb' : ((bO ⟨s, hs⟩ : c.O) : Qbar l) = b s` using `rfl`. Establish `hk'' : (((θ ⟨s, hs⟩ : c.Oˣ) : c.O) : Qbar l) = k s` using `hθ _`. Move the coercions through the operations in `[hb', hk'']`. Clear the denominators using the available nonvanishing facts. Rewrite `e` using `[e2, norm_mul]`.

Establish `e3 : ‖((l : ℕ) : Qbar l) ^ (n + 1)‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ n`. Rewrite using `[norm_pow]`. Conclude with `pow_le_pow_of_le_one (norm_nonneg _) hl1.le (Nat.le_succ n)`. Rewrite `e` using `[← le_div_iff₀' hm]`. Use `e.trans ?_` and prove the remaining obligations.

Rewrite using `[div_le_iff₀ hm]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem GlobalTheory.Ord2.localDuality_char : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' a b : G ℚ Ω → Qbar l), OverL l A → ContinuousOn k (Dec (F := ℚ) A) → ContinuousOn k' (Dec (F := ℚ) A) → ContinuousOn a (Dec (F := ℚ) A) → ContinuousOn b (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ a s ∈ c.O ∧ b s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t ∧ k' (s * t) = k' s * k' t ∧ b (s * t) = b s + k s * b t ∧ a (s * t) = a s + k' s * a t) → (∃ s ∈ Dec (F := ℚ) A, k s ≠ 1) → (∃ s ∈ Dec (F := ℚ) A, k' s ≠ 1) → (∀ n : ℕ, Cob2 c n (Dec (F := ℚ) A) (fun s t => b s * (k' s * a t))) → (∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, b s = k s * x - x) ∨ ∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, a s = k' s * x - x := by
  intro hL l _ Ω _ _ _ c A k k' a b hA hk hk' ha hb hint hmul hk1 hk'1 hcob
  by_cases hac : ∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, a s = k' s * x - x
  · exact Or.inr hac
  left
  obtain ⟨θ, hθc, hθ⟩ := GlobalTheory.T.exists_unitCharacter_of_integral_cyclotomic_product l Ω c A k k' hk
    (fun s hs => ⟨(hint s hs).1, (hint s hs).2.1, (hint s hs).2.2.2.2⟩) (fun s hs t ht => (hmul s hs t ht).1)
  obtain ⟨θ', hθ'c, hθ'⟩ := GlobalTheory.T.exists_unitCharacter_of_integral_cyclotomic_product l Ω c A k' k hk'
    (fun s hs => ⟨(hint s hs).2.1, (hint s hs).1, by rw [mul_comm]; exact (hint s hs).2.2.2.2⟩)
    (fun s hs t ht => (hmul s hs t ht).2.1)
  have hN := GlobalTheory.T.norm_le_pow_iff_dvd l c
  have hchi : ∀ s : G ℚ Ω, ((((UpperTheory.V.Base.chiO ℚ Ω l c.O) s : c.Oˣ) : c.O) : Qbar l) = eps l s := by
    intro s; rfl
  have hcyc : θ * θ' = (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype := by
    refine MonoidHom.ext fun g => Units.ext (Subtype.ext ?_)
    simp only [MonoidHom.mul_apply, Units.val_mul, Subalgebra.coe_mul, hθ, hθ', MonoidHom.comp_apply,
      Subgroup.coe_subtype, hchi]
    exact (hint g g.2).2.2.2.2
  have hθ1 : ∃ g, θ g ≠ 1 := by
    obtain ⟨s, hs, hne⟩ := hk1
    exact ⟨⟨s, hs⟩, fun h => hne (by have e := hθ ⟨s, hs⟩; rw [h] at e; exact e.symm.trans rfl)⟩
  have hθ'1 : ∃ g, θ' g ≠ 1 := by
    obtain ⟨s, hs, hne⟩ := hk'1
    exact ⟨⟨s, hs⟩, fun h => hne (by have e := hθ' ⟨s, hs⟩; rw [h] at e; exact e.symm.trans rfl)⟩
  have hθ'ne : ∃ g, θ' g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g := by
    obtain ⟨s, hs, hne⟩ := hk1
    refine ⟨⟨s, hs⟩, fun h => hne ?_⟩
    have e := DFunLike.congr_fun hcyc ⟨s, hs⟩
    rw [MonoidHom.mul_apply, ← h] at e
    have e1 : θ ⟨s, hs⟩ = 1 := mul_eq_right.1 e
    have e2 := hθ ⟨s, hs⟩; rw [e1] at e2; exact e2.symm.trans rfl
  set p : c.O := ((l : ℕ) : c.O) with hp
  let aO : ↥(Dec (F := ℚ) A) → c.O := fun s => ⟨a s, (hint s.1 s.2).2.2.1⟩
  let bO : ↥(Dec (F := ℚ) A) → c.O := fun s => ⟨b s, (hint s.1 s.2).2.2.2.1⟩
  have haO : Continuous aO := (continuousOn_iff_continuous_domRestrict.1 ha).subtype_mk _
  have hbO : Continuous bO := (continuousOn_iff_continuous_domRestrict.1 hb).subtype_mk _
  have haOc : ∀ s t, aO (s * t) = aO s + ((θ' s : c.Oˣ) : c.O) * aO t := fun s t => Subtype.ext (by
    simp only [aO, Subalgebra.coe_add, Subalgebra.coe_mul, hθ']
    exact (hmul s.1 s.2 t.1 t.2).2.2.2)
  have hbOc : ∀ s t, bO (s * t) = bO s + ((θ s : c.Oˣ) : c.O) * bO t := fun s t => Subtype.ext (by
    simp only [bO, Subalgebra.coe_add, Subalgebra.coe_mul, hθ]
    exact (hmul s.1 s.2 t.1 t.2).2.2.1)
  have hnorm1 : ∀ x : c.O, ‖((x : c.O) : Qbar l)‖ ≤ 1 := fun x => by
    have := (hN 0 x).2 (by simp); simpa using this
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_annihilatorDepth_of_not_coboundary l (Set.univ : Set ↥(Dec (F := ℚ) A)) (fun s => k' s) (fun s => a s)
    (by obtain ⟨s, hs, hne⟩ := hk'1; exact ⟨⟨s, hs⟩, trivial, hne⟩)
    (fun ⟨X, hX⟩ => hac ⟨X, fun s hs => hX ⟨s, hs⟩ trivial⟩)
  have hann : ∀ n : ℕ, ∀ x y : c.O, (∀ s, p ^ n ∣ x * aO s - (((θ' s : c.Oˣ) : c.O) * y - y)) → p ^ (n - r) ∣ x := by
    intro n x y h
    refine (hN (n - r) x).1 (hr n x y (hnorm1 x) fun s _ => ?_)
    have := (hN n _).2 (h s)
    simpa [aO, hθ'] using this
  obtain ⟨m, hm0, hAF⟩ := GlobalTheory.T.exists_mul_scalarClass_eq_smul_add_coboundary_modPrimePow hL.lf hL.lt hL.le l Ω c A hA θ' hθ'c hθ'1 hθ'ne r
  have key : ∀ n : ℕ, 1 ≤ n → ∃ x : c.O, ∀ s, p ^ n ∣ (m : c.O) * bO s - (((θ s : c.Oˣ) : c.O) * x - x) := by
    intro n hn
    refine GlobalTheory.T.coboundary_of_orthogonal_dualCharacter_modPrimePow hL.lf hL.lt l Ω c A hA θ θ' hθc hθ'c hcyc n hn (fun s => (m : c.O) * bO s)
      (continuous_const.mul hbO) (fun s t => ?_) (fun a' ha' hca' => ?_)
    · rw [hbOc s t]; ring_nf; exact dvd_zero _
    obtain ⟨x, y, hxy⟩ := hAF n hn aO haO (fun s t => by rw [haOc s t, sub_self]; exact dvd_zero _)
      (hann n) a' ha' hca'
    obtain ⟨u, huc, huO, hu⟩ := hcob n
    let u0 : ↥(Dec (F := ℚ) A) → c.O := fun s => ⟨u s, huO s⟩
    have hu0c : Continuous u0 := (continuousOn_iff_continuous_domRestrict.1 huc).subtype_mk _
    have hu0 : ∀ s t, p ^ n ∣ bO s * (((θ' s : c.Oˣ) : c.O) * aO t) -
        ((((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O)) * u0 t - u0 (s * t) + u0 s) := by
      intro s t
      refine (hN n _).1 ?_
      have e : ‖b s.1 * (k' s.1 * a t.1) - (eps l s.1 * u t.1 - u (s.1 * t.1) + u s.1)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ :=
        hu s.1 s.2 t.1 t.2
      have he : k s.1 * k' s.1 = eps l s.1 := (hint s.1 s.2).2.2.2.2
      rw [← he] at e
      convert e using 2
      simp only [aO, bO, u0, Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul, hθ, hθ']
      rfl
    have hbt : Continuous (fun s => bO s * ((θ' s : c.Oˣ) : c.O)) := hbO.mul hθ'c
    have hcu : Continuous (fun s => x * u0 s - bO s * ((θ' s : c.Oˣ) : c.O) * y) :=
      (continuous_const.mul hu0c).sub (hbt.mul continuous_const)
    refine ⟨fun s => x * u0 s - bO s * ((θ' s : c.Oˣ) : c.O) * y, hcu, fun s t => ?_⟩
    obtain ⟨q1, hq1⟩ := hxy t
    obtain ⟨q2, hq2⟩ := hu0 s t
    refine ⟨bO s * ((θ' s : c.Oˣ) : c.O) * q1 + x * q2, ?_⟩
    simp only []
    rw [hbOc s t, map_mul θ' s t, Units.val_mul]
    linear_combination (bO s * ((θ' s : c.Oˣ) : c.O)) * hq1 + x * hq2
  obtain ⟨s0, hs0, hne0⟩ := hk1
  refine GlobalTheory.T.coboundary_of_uniform_limit_coboundaries (Dec (F := ℚ) A : Set (G ℚ Ω)) k b ⟨s0, hs0, hne0⟩ fun ε hε => ?_
  have hl1 : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
    rw [e, norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hm : (0 : ℝ) < ‖((m : ℕ) : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hm0.ne')
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (mul_pos hε hm) hl1
  obtain ⟨x, hx⟩ := key (n + 1) (Nat.le_add_left 1 n)
  refine ⟨(x : Qbar l) / (m : Qbar l), fun s hs => ?_⟩
  have e := (hN (n + 1) _).2 (hx ⟨s, hs⟩)
  have e2 : ((((m : c.O) * bO ⟨s, hs⟩ - (((θ ⟨s, hs⟩ : c.Oˣ) : c.O) * x - x) : c.O)) : Qbar l) =
      (m : Qbar l) * (b s - (k s * ((x : Qbar l) / (m : Qbar l)) - (x : Qbar l) / (m : Qbar l))) := by
    have hm' : (m : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hm0.ne'
    have hb' : ((bO ⟨s, hs⟩ : c.O) : Qbar l) = b s := rfl
    have hk'' : (((θ ⟨s, hs⟩ : c.Oˣ) : c.O) : Qbar l) = k s := hθ _
    push_cast [hb', hk'']
    field_simp
  rw [e2, norm_mul] at e
  have e3 : ‖((l : ℕ) : Qbar l) ^ (n + 1)‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ n := by
    rw [norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hl1.le (Nat.le_succ n)
  rw [← le_div_iff₀' hm] at e
  refine e.trans ?_
  rw [div_le_iff₀ hm]
  linarith
