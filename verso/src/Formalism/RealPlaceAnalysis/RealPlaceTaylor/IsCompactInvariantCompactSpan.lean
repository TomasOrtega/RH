import Formalism.RealPlaceAnalysis.StatementKT

open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

section KT2Gen
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}

/- English proof (translation)
Conclude with `Submodule.mem_sInf.2 fun S hS => hS.1`.
-/
theorem mem_compactSpan (x : V) : x ∈ kSpan ε F x := by
  exact Submodule.mem_sInf.2 fun S hS => hS.1

/- English proof (translation)
The claim follows from `sInf_le ⟨hx, hS⟩`.
-/
theorem compactSpan_le {x : V} {S : Submodule ℂ V} (hx : x ∈ S) (hS : KStable ε F S) :
    kSpan ε F x ≤ S := sInf_le ⟨hx, hS⟩

/- English proof (translation)
Introduce `a b hab y hy`. Rewrite `hy`, the goal using `[kSpan, Submodule.mem_sInf]`. Introduce `S hS`. Conclude with `hS.2 a b hab y (hy S hS)`.
-/
theorem isCompactInvariant_compactSpan (x : V) : KStable ε F (kSpan ε F x) := by
  intro a b hab y hy
  rw [kSpan, Submodule.mem_sInf] at hy ⊢
  intro S hS
  exact hS.2 a b hab y (hy S hS)

/- English proof (translation)
Introduce `c`. Establish `h` using `congrArg (fun T : Module.End ℂ V => T v) (hrel c c a b rfl hab)`. Establish `e1 : (if c = a then F c b else 0) v = (if c = a then (1 : ℂ) else 0) • F a b v` using `by split_ifs with h1`. Substitute `h1` using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish `e2 : (if b = c then F a c else 0) v = (if c = b then (1 : ℂ) else 0) • F a b v`. Distinguish the cases in `h2 : c = b`. Substitute `h2` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h2, Ne.symm h2]`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hv c, map_smul, e1, e2] at h`. Rewrite `h` using `[sub_eq_iff_eq_add]`. Rewrite using `[h, ← sub_smul, ← add_smul]`. Use `congr 1`.

Simplify using `only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`.
-/
theorem isWeightVector_apply (hrel : KRel ε F) {ν : Fin n → ℝ} {v : V}
    (hv : IsWeight F ν v) (a b : Fin n) (hab : ε a = ε b) :
    IsWeight F (ν + root a b) (F a b v) := by
  intro c
  have h := congrArg (fun T : Module.End ℂ V => T v) (hrel c c a b rfl hab)
  have e1 : (if c = a then F c b else 0) v = (if c = a then (1 : ℂ) else 0) • F a b v := by
    split_ifs with h1
    · subst h1
      simp
    · simp
  have e2 : (if b = c then F a c else 0) v = (if c = b then (1 : ℂ) else 0) • F a b v := by
    by_cases h2 : c = b
    · subst h2
      simp
    · simp [h2, Ne.symm h2]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv c, map_smul, e1, e2] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h, ← sub_smul, ← add_smul]
  congr 1
  simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> push_cast <;> ring

end KT2Gen

/- English proof (translation)
Establish `h` using `hunit a a rfl v v`. Rewrite `h` using `[hc, inner_smul_left, inner_smul_right]`. Establish `hvv : ⟪v, v⟫_ℂ ≠ 0` using `inner_self_ne_zero.2 hv`. Conclude with `Complex.conj_eq_iff_re.1 (mul_right_cancel₀ hvv h)`.
-/
theorem eigenvalue_real {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {F : Fin n → Fin n → Module.End ℂ V} (hunit : KUnit ε F)
    {v : V} (hv : v ≠ 0) (a : Fin n) {c : ℂ} (hc : F a a v = c • v) : ((c.re : ℝ) : ℂ) = c := by
  have h := hunit a a rfl v v
  rw [hc, inner_smul_left, inner_smul_right] at h
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv
  exact Complex.conj_eq_iff_re.1 (mul_right_cancel₀ hvv h)

/- English proof (translation)
Introduce `V _ _ n ε F μ ν x y hrel hunit hx hyx hy`. Distinguish the cases in `hμν : ν = μ`. Use `right`. Use `⟨hμν, ?_⟩` and prove the remaining obligations. Take `⟨hspan, huniq⟩` from `hl V n ε F μ x hrel hx`.

Conclude with `huniq y (hspan ▸ hyx) (hμν ▸ hy.1)`. Use `left`. Establish `h0` using `ho V n ε F μ ν x y hrel hunit hx hy (Ne.symm hμν) y hyx y (mem_compactSpan y)`. Conclude with `inner_self_eq_zero.1 h0`.
-/
theorem kHiUniq_of (hl : KLow) (_hw : KWtOrth) (ho : KOrth) : KHiUniq := by
  intro V _ _ n ε F μ ν x y hrel hunit hx hyx hy
  by_cases hμν : ν = μ
  · right
    refine ⟨hμν, ?_⟩
    obtain ⟨hspan, huniq⟩ := hl V n ε F μ x hrel hx
    exact huniq y (hspan ▸ hyx) (hμν ▸ hy.1)
  · left
    have h0 := ho V n ε F μ ν x y hrel hunit hx hy (Ne.symm hμν) y hyx y (mem_compactSpan y)
    exact inner_self_eq_zero.1 h0

/- English proof (translation)
Introduce `V _ _ n ε F μ x hfd hrel hunit hx S hS hSst`. Distinguish the cases in `h0 : S = ⊥`. Conclude with `Or.inl h0`. Use `right`. Use `haveI := hfd`.

Establish `hfdS : FiniteDimensional ℂ S` using `Submodule.finiteDimensional_of_le hS`. Take `⟨y, hyS, hy0, ν, hy⟩` from `he V n ε F S hfdS hrel hunit hSst h0`. Break down `hu V n ε F μ ν x y hrel hunit hx (hS hyS) hy with h | ⟨-, c, hc⟩` into its components or cases. Conclude with `absurd h hy0`. Establish `hc0 : c ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hc` using `[zero_smul]`. Conclude with `hy0 hc`. Establish `hxS : x ∈ S`. Establish `h1 : c⁻¹ • y ∈ S` using `S.smul_mem _ hyS`.

Rewrite `h1` using `[hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Then use the resulting hypothesis. Conclude with `le_antisymm hS (compactSpan_le hxS hSst)`.
-/
theorem kIrr_of (he : KHiExist) (hu : KHiUniq) : KIrr := by
  intro V _ _ n ε F μ x hfd hrel hunit hx S hS hSst
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  right
  haveI := hfd
  have hfdS : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hS
  obtain ⟨y, hyS, hy0, ν, hy⟩ := he V n ε F S hfdS hrel hunit hSst h0
  rcases hu V n ε F μ ν x y hrel hunit hx (hS hyS) hy with h | ⟨-, c, hc⟩
  · exact absurd h hy0
  · have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hy0 hc
    have hxS : x ∈ S := by
      have h1 : c⁻¹ • y ∈ S := S.smul_mem _ hyS
      rwa [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at h1
    exact le_antisymm hS (compactSpan_le hxS hSst)

/- English proof (translation)
Simplify using `only [root, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weighted_sum_rootVector_shift {n : ℕ} (ν : Fin n → ℝ) (a b : Fin n) :
    (∑ i : Fin n, -((i : ℕ) : ℝ) * (ν + root a b) i) =
      (∑ i : Fin n, -((i : ℕ) : ℝ) * ν i) + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  simp only [root, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

/- English proof (translation)
Introduce `V _ _ n ε F S hfd hrel hunit hst hne`. Use `haveI := hfd`. Establish `hcomm : ∀ a b : Fin n, F a a * F b b = F b b * F a a`. Introduce `a b`. Establish `h` using `hrel a a b b rfl rfl`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Both sides reduce to the same expression. Simplify `h` using `[hab, Ne.symm hab, sub_eq_zero]`. Establish `main : ∀ s : Finset (Fin n), ∃ W : Submodule ℂ V, W ≤ S ∧ W ≠ ⊥ ∧ (∀ a, ∀ w ∈ W, F a a w ∈ W) ∧ ∃ lam : Fin n → ℂ, ∀ a ∈ s, ∀ w ∈ W, F a a w = lam a • w`.

Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨S, le_rfl, hne, fun a w hw => hst a a rfl w hw, 0, by simp⟩`. Consider the case `@insert a s ha ih`. Take `⟨W, hWS, hW0, hWst, lam, hlam⟩` from `ih`.

Use `haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWS`. Use `haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW0`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue ((F a a).restrict (hWst a))`. Take `⟨⟨v, hvW⟩, hv⟩` from `hc.exists_hasEigenvector`. Establish `hker : ∀ y, y ∈ LinearMap.ker (F a a - c • 1) ↔ F a a y = c • y`.

Introduce `y`. Simplify using `only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Establish `hvker : F a a v = c • v`. Establish `h1` using `congrArg Subtype.val hv.apply_eq_smul`. Simplify using `using h1`.

Use `⟨W ⊓ LinearMap.ker (F a a - c • 1), inf_le_left.trans hWS, ?_, ?_, Function.update lam a c, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `hvmem : v ∈ W ⊓ LinearMap.ker (F a a - c • 1)` using `⟨hvW, (hker v).2 hvker⟩`. Rewrite `hvmem` using `[h]`. Conclude with `hv.2 (Subtype.ext (by simpa using (Submodule.mem_bot ℂ).1 hvmem))`.

Introduce `b w hw`. Use `⟨hWst b w hw.1, (hker _).2 ?_⟩` and prove the remaining obligations. Establish `h1 : F a a w = c • w` using `(hker w).1 hw.2`. Establish `h2` using `congrArg (fun T : Module.End ℂ V => T w) (hcomm a b)`. Simplify using `only [Module.End.mul_apply] at h2`.

Rewrite using `[h2, h1, map_smul]`. Introduce `b hb w hw`. Break down `Finset.mem_insert.1 hb with rfl | hb'` into its components or cases. Rewrite using `[Function.update_self]`. Conclude with `(hker w).1 hw.2`.

Rewrite using `[Function.update_of_ne (by rintro rfl; exact ha hb')]`. Conclude with `hlam b hb' w hw.1`. Take `⟨W, hWS, hW0, -, lam, hlam⟩` from `main Finset.univ`. Take `⟨v0, hv0W, hv00⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW0`. Establish `hw0 : IsWeight F (fun a => (lam a).re) v0` using `fun a => by`.

Rewrite using `[eigenvalue_real hunit hv00 a (hlam a (Finset.mem_univ a) v0 hv0W)]`. Conclude with `hlam a (Finset.mem_univ a) v0 hv0W`. Establish `hstab : ∀ a, ∀ y ∈ S, F a a y ∈ S` using `fun a => hst a a rfl`. Establish `hfinW : {ν : Fin n → ℝ | ∃ v ∈ S, v ≠ 0 ∧ IsWeight F ν v}.Finite`. Use `(Set.Finite.pi (t := fun a => {r : ℝ | Module.End.HasEigenvalue ((F a a).restrict (hstab a)) (r : ℂ)}) (fun a => ?_)).subset ?_` and prove the remaining obligations.

Conclude with `(Module.End.finite_hasEigenvalue _).preimage (fun _ _ _ _ h => Complex.ofReal_injective h)`. Introduce and unpack `ν ⟨v, hvS, hv0, hvw⟩`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]`. Introduce `a`. Apply `Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvS⟩)` to reduce the goal to its premises.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.End.mem_eigenspace_iff]`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hvw a]`. Introduce `h`.

Apply `hv0` to reduce the goal to its premises. Simplify using `using congrArg Subtype.val h`. Take `⟨ν, ⟨v, hvS, hv0, hvw⟩, hmax⟩` from `Set.exists_max_image _ (fun ν : Fin n → ℝ => ∑ i : Fin n, -((i : ℕ) : ℝ) * ν i) hfinW ⟨_, v0, hWS hv0W, hv00, hw0⟩`. Use `⟨v, hvS, hv0, ν, hvw, fun a b hab hεab => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne'`.

Establish `hmem : ν + root a b ∈ {ν : Fin n → ℝ | ∃ v ∈ S, v ≠ 0 ∧ IsWeight F ν v}` using `⟨F a b v, hst a b hεab v hvS, hne', isWeightVector_apply hrel hvw a b hεab⟩`. Establish `h1` using `hmax _ hmem`. Rewrite `h1` using `[weighted_sum_rootVector_shift]`. Establish `h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast hab`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem highestWeightExists_holds : KHiExist := by
  intro V _ _ n ε F S hfd hrel hunit hst hne
  haveI := hfd
  have hcomm : ∀ a b : Fin n, F a a * F b b = F b b * F a a := by
    intro a b
    have h := hrel a a b b rfl rfl
    by_cases hab : a = b
    · subst hab
      rfl
    · simpa [hab, Ne.symm hab, sub_eq_zero] using h
  have main : ∀ s : Finset (Fin n), ∃ W : Submodule ℂ V, W ≤ S ∧ W ≠ ⊥ ∧
      (∀ a, ∀ w ∈ W, F a a w ∈ W) ∧ ∃ lam : Fin n → ℂ, ∀ a ∈ s, ∀ w ∈ W, F a a w = lam a • w := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨S, le_rfl, hne, fun a w hw => hst a a rfl w hw, 0, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨W, hWS, hW0, hWst, lam, hlam⟩ := ih
      haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWS
      haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW0
      obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((F a a).restrict (hWst a))
      obtain ⟨⟨v, hvW⟩, hv⟩ := hc.exists_hasEigenvector
      have hker : ∀ y, y ∈ LinearMap.ker (F a a - c • 1) ↔ F a a y = c • y := by
        intro y
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          sub_eq_zero]
      have hvker : F a a v = c • v := by
        have h1 := congrArg Subtype.val hv.apply_eq_smul
        simpa using h1
      refine ⟨W ⊓ LinearMap.ker (F a a - c • 1), inf_le_left.trans hWS, ?_, ?_, Function.update lam a c, ?_⟩
      · intro h
        have hvmem : v ∈ W ⊓ LinearMap.ker (F a a - c • 1) := ⟨hvW, (hker v).2 hvker⟩
        rw [h] at hvmem
        exact hv.2 (Subtype.ext (by simpa using (Submodule.mem_bot ℂ).1 hvmem))
      · intro b w hw
        refine ⟨hWst b w hw.1, (hker _).2 ?_⟩
        have h1 : F a a w = c • w := (hker w).1 hw.2
        have h2 := congrArg (fun T : Module.End ℂ V => T w) (hcomm a b)
        simp only [Module.End.mul_apply] at h2
        rw [h2, h1, map_smul]
      · intro b hb w hw
        rcases Finset.mem_insert.1 hb with rfl | hb'
        · rw [Function.update_self]
          exact (hker w).1 hw.2
        · rw [Function.update_of_ne (by rintro rfl; exact ha hb')]
          exact hlam b hb' w hw.1
  obtain ⟨W, hWS, hW0, -, lam, hlam⟩ := main Finset.univ
  obtain ⟨v0, hv0W, hv00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hw0 : IsWeight F (fun a => (lam a).re) v0 := fun a => by
    rw [eigenvalue_real hunit hv00 a (hlam a (Finset.mem_univ a) v0 hv0W)]
    exact hlam a (Finset.mem_univ a) v0 hv0W
  have hstab : ∀ a, ∀ y ∈ S, F a a y ∈ S := fun a => hst a a rfl
  have hfinW : {ν : Fin n → ℝ | ∃ v ∈ S, v ≠ 0 ∧ IsWeight F ν v}.Finite := by
    refine (Set.Finite.pi (t := fun a => {r : ℝ | Module.End.HasEigenvalue ((F a a).restrict (hstab a)) (r : ℂ)})
      (fun a => ?_)).subset ?_
    · exact (Module.End.finite_hasEigenvalue _).preimage (fun _ _ _ _ h => Complex.ofReal_injective h)
    · rintro ν ⟨v, hvS, hv0, hvw⟩
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
      intro a
      apply Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvS⟩)
      refine ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff]
        apply Subtype.ext
        simp [hvw a]
      · intro h
        apply hv0
        simpa using congrArg Subtype.val h
  obtain ⟨ν, ⟨v, hvS, hv0, hvw⟩, hmax⟩ := Set.exists_max_image _
    (fun ν : Fin n → ℝ => ∑ i : Fin n, -((i : ℕ) : ℝ) * ν i) hfinW ⟨_, v0, hWS hv0W, hv00, hw0⟩
  refine ⟨v, hvS, hv0, ν, hvw, fun a b hab hεab => ?_⟩
  by_contra hne'
  have hmem : ν + root a b ∈ {ν : Fin n → ℝ | ∃ v ∈ S, v ≠ 0 ∧ IsWeight F ν v} :=
    ⟨F a b v, hst a b hεab v hvS, hne', isWeightVector_apply hrel hvw a b hεab⟩
  have h1 := hmax _ hmem
  rw [weighted_sum_rootVector_shift] at h1
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

end Formalism.REAL
