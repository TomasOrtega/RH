import Mathlib

open scoped ComplexConjugate

namespace GlobalTheory.ChainOnto

/- English proof (translation)
Set `Q : A → Prop` to `fun u => ∃ (s : Finset I) (v : I → A), (∀ i ∈ s, pA (v i) i) ∧ (∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ¬ RA i i') ∧ u = ∑ i ∈ s, v i`. Establish `hQ0 : Q 0` using `⟨∅, fun _ => 0, by simp, by simp, by simp⟩`. Establish `hadd1 : ∀ u w B, Q u → pA w B → Q (u + w)`. Introduce and unpack `u w B ⟨s, v, hv, hp, rfl⟩ hw`. Distinguish the cases in `hex : ∃ i ∈ s, RA i B`.

Take `⟨i, hi, hiB⟩` from `hex`. Distinguish the cases in `hz : v i + w = 0`. Use `⟨s.erase i, v, fun j hj => hv j (Finset.mem_of_mem_erase hj), fun j hj j' hj' => hp j (Finset.mem_of_mem_erase hj) j' (Finset.mem_of_mem_erase hj'), ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.add_sum_erase s v hi]`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨s, Function.update v i (v i + w), ?_, hp, ?_⟩` and prove the remaining obligations. Introduce `j hj`. Distinguish the cases in `hji : j = i`. Substitute `hji` using the available equality. Simplify using `only [Function.update_self]`.

Use `hmerge (v j) w j B 1 (hv j hj) hw hiB (by simpa using hz)` as an intermediate fact. Simplify using `using this`. Rewrite using `[Function.update_of_ne hji]`. Conclude with `hv j hj`. Rewrite using `[← Finset.add_sum_erase s (Function.update v i (v i + w)) hi, ← Finset.add_sum_erase s v hi]`.

Simplify using `only [Function.update_self]`. Rewrite using `[Finset.sum_congr rfl (fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _)]`. Normalize the expressions using the abelian group laws. Use `push_neg at hex`. Establish `hBs : B ∉ s` using `fun hB => hex B hB (hRA.refl B)`.

Use `⟨insert B s, Function.update v B w, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_insert]`. Break down `hj with hj | hj` into its components or cases. Substitute `hj` using the available equality.

Simplify using `using hw`. Establish `hjB : j ≠ B` using `fun h => hBs (by rw [← h]; exact hj)`. Rewrite using `[Function.update_of_ne hjB]`. Conclude with `hv j hj`. Introduce `j hj j' hj' hne`.

Rewrite `hj`, `hj'` using `[Finset.mem_insert]`. Apply the tactic sequence `rcases hj with hj | hj <;> rcases hj' with hj' | hj'`. Conclude with `absurd (hj.trans hj'.symm) hne`. Substitute `hj` using the available equality. Conclude with `fun h => hex j' hj' (hRA.symm h)`.

Substitute `hj'` using the available equality. Conclude with `hex j hj`. Conclude with `hp j hj j' hj' hne`. Rewrite using `[Finset.sum_insert hBs, Function.update_self, Finset.sum_congr rfl (fun j hj => Function.update_of_ne (show j ≠ B from fun h => hBs (by rw [← h]; exact hj)) w v)]`. Normalize the expressions using the abelian group laws.

Establish `haddS : ∀ (s' : Finset I) (v' : I → A) u, Q u → (∀ i ∈ s', pA (v' i) i) → Q (u + ∑ i ∈ s', v' i)`. Introduce `s' v'`. Proceed by induction on `s' using Finset.induction_on with`. Consider the case `empty => intro u hu _`. Simplify using `using hu`.

Consider the case `insert a s ha ih`. Introduce `u hu hv'`. Rewrite using `[Finset.sum_insert ha, ← add_assoc]`. Conclude with `ih _ (hadd1 u (v' a) a hu (hv' a (Finset.mem_insert_self a s))) (fun i hi => hv' i (Finset.mem_insert_of_mem hi))`. Establish `hadd : ∀ u u', Q u → Q u' → Q (u + u')`.

Introduce and unpack `u u' hu ⟨s', v', hv', -, rfl⟩`. Conclude with `haddS s' v' u hu hv'`. Establish `hsm : ∀ (a : ℂ) u, Q u → Q (a • u)`. Introduce and unpack `a u ⟨s, v, hv, hp, rfl⟩`. Distinguish the cases in `ha : a = 0`.

Substitute `ha` using the available equality. Simplify using `using hQ0`. Conclude with `⟨s, fun i => a • v i, fun i hi => hsmul _ _ a (hv i hi) ha, hp, by rw [Finset.smul_sum]⟩`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨B, hB⟩` from `hx`. Simplify using `using hadd1 0 x B hQ0 hB`. Consider the case `zero => exact hQ0`. Consider the case `add x y _ _ hx hy => exact hadd x y hx hy`. Consider the case `smul a x _ hx => exact hsm a x hx`.
-/
theorem exists_sum_pairwise_unrelated {A I : Type} [AddCommGroup A] [Module ℂ A]
    (pA : A → I → Prop) (RA : I → I → Prop) (hRA : Equivalence RA)
    (hmerge : ∀ u u' B B' (a : ℂ), pA u B → pA u' B' → RA B B' → u + a • u' ≠ 0 → pA (u + a • u') B)
    (hsmul : ∀ u B (a : ℂ), pA u B → a ≠ 0 → pA (a • u) B) (u : A)
    (hu : u ∈ Submodule.span ℂ {u | ∃ B, pA u B}) :
    ∃ (s : Finset I) (v : I → A), (∀ i ∈ s, pA (v i) i) ∧
      (∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ¬ RA i i') ∧ u = ∑ i ∈ s, v i := by
  classical
  let Q : A → Prop := fun u => ∃ (s : Finset I) (v : I → A), (∀ i ∈ s, pA (v i) i) ∧
      (∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ¬ RA i i') ∧ u = ∑ i ∈ s, v i
  have hQ0 : Q 0 := ⟨∅, fun _ => 0, by simp, by simp, by simp⟩
  have hadd1 : ∀ u w B, Q u → pA w B → Q (u + w) := by
    rintro u w B ⟨s, v, hv, hp, rfl⟩ hw
    by_cases hex : ∃ i ∈ s, RA i B
    · obtain ⟨i, hi, hiB⟩ := hex
      by_cases hz : v i + w = 0
      · refine ⟨s.erase i, v, fun j hj => hv j (Finset.mem_of_mem_erase hj),
          fun j hj j' hj' => hp j (Finset.mem_of_mem_erase hj) j' (Finset.mem_of_mem_erase hj'), ?_⟩
        rw [← Finset.add_sum_erase s v hi]
        calc v i + ∑ x ∈ s.erase i, v x + w = (v i + w) + ∑ x ∈ s.erase i, v x := by abel
          _ = _ := by rw [hz, zero_add]
      · refine ⟨s, Function.update v i (v i + w), ?_, hp, ?_⟩
        · intro j hj
          by_cases hji : j = i
          · subst hji
            simp only [Function.update_self]
            have := hmerge (v j) w j B 1 (hv j hj) hw hiB (by simpa using hz)
            simpa using this
          · rw [Function.update_of_ne hji]; exact hv j hj
        · rw [← Finset.add_sum_erase s (Function.update v i (v i + w)) hi, ← Finset.add_sum_erase s v hi]
          simp only [Function.update_self]
          rw [Finset.sum_congr rfl (fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _)]
          abel
    · push_neg at hex
      have hBs : B ∉ s := fun hB => hex B hB (hRA.refl B)
      refine ⟨insert B s, Function.update v B w, ?_, ?_, ?_⟩
      · intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with hj | hj
        · subst hj; simpa using hw
        · have hjB : j ≠ B := fun h => hBs (by rw [← h]; exact hj)
          rw [Function.update_of_ne hjB]; exact hv j hj
      · intro j hj j' hj' hne
        rw [Finset.mem_insert] at hj hj'
        rcases hj with hj | hj <;> rcases hj' with hj' | hj'
        · exact absurd (hj.trans hj'.symm) hne
        · subst hj; exact fun h => hex j' hj' (hRA.symm h)
        · subst hj'; exact hex j hj
        · exact hp j hj j' hj' hne
      · rw [Finset.sum_insert hBs, Function.update_self,
          Finset.sum_congr rfl (fun j hj => Function.update_of_ne (show j ≠ B from fun h => hBs (by rw [← h]; exact hj)) w v)]
        abel
  have haddS : ∀ (s' : Finset I) (v' : I → A) u, Q u → (∀ i ∈ s', pA (v' i) i) →
      Q (u + ∑ i ∈ s', v' i) := by
    intro s' v'
    induction s' using Finset.induction_on with
    | empty => intro u hu _; simpa using hu
    | insert a s ha ih =>
      intro u hu hv'
      rw [Finset.sum_insert ha, ← add_assoc]
      exact ih _ (hadd1 u (v' a) a hu (hv' a (Finset.mem_insert_self a s)))
        (fun i hi => hv' i (Finset.mem_insert_of_mem hi))
  have hadd : ∀ u u', Q u → Q u' → Q (u + u') := by
    rintro u u' hu ⟨s', v', hv', -, rfl⟩
    exact haddS s' v' u hu hv'
  have hsm : ∀ (a : ℂ) u, Q u → Q (a • u) := by
    rintro a u ⟨s, v, hv, hp, rfl⟩
    by_cases ha : a = 0
    · subst ha; simpa using hQ0
    · exact ⟨s, fun i => a • v i, fun i hi => hsmul _ _ a (hv i hi) ha, hp, by rw [Finset.smul_sum]⟩
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨B, hB⟩ := hx
    simpa using hadd1 0 x B hQ0 hB
  | zero => exact hQ0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul a x _ hx => exact hsm a x hx

/- English proof (translation)
Set `b` to `Module.finBasis ℂ S`. Set `f : A →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ)` to `{ toFun := fun u i => ipA u (b i : A) map_add' := by intro x y; ext i; simp map_smul' := by intro a x; ext i; simp }`. Establish `hlt : Module.finrank ℂ (Fin (Module.finrank ℂ S) → ℂ) < Module.finrank ℂ A`. Rewrite using `[Module.finrank_fin_fun]`. Conclude with `Submodule.finrank_lt hS`.

Establish `hker` using `LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt`. Take `⟨u, hu, hu0⟩` from `(Submodule.ne_bot_iff _).mp hker`. Use `⟨u, hu0, fun s hs => ?_⟩` and prove the remaining obligations. Establish `hzero : (ipA u).comp S.subtype = 0`. Use `b.ext fun i => ?_` and prove the remaining obligations.

Use `congrFun (LinearMap.mem_ker.mp hu) i` as an intermediate fact. Simplify `this` using `[f]`. Establish `: ipA u s = 0`. Use `LinearMap.congr_fun hzero ⟨s, hs⟩` as an intermediate fact. Simplify using `using this`.

Rewrite using `[hsym, this, map_zero]`.
-/
theorem exists_ne_zero_orth {A : Type} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (hsym : ∀ x y, ipA x y = conj (ipA y x))
    (S : Submodule ℂ A) (hS : S ≠ ⊤) : ∃ u : A, u ≠ 0 ∧ ∀ s ∈ S, ipA s u = 0 := by
  classical
  let b := Module.finBasis ℂ S
  let f : A →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    { toFun := fun u i => ipA u (b i : A)
      map_add' := by intro x y; ext i; simp
      map_smul' := by intro a x; ext i; simp }
  have hlt : Module.finrank ℂ (Fin (Module.finrank ℂ S) → ℂ) < Module.finrank ℂ A := by
    rw [Module.finrank_fin_fun]
    exact Submodule.finrank_lt hS
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨u, hu0, fun s hs => ?_⟩
  have hzero : (ipA u).comp S.subtype = 0 := by
    refine b.ext fun i => ?_
    have := congrFun (LinearMap.mem_ker.mp hu) i
    simpa [f] using this
  have : ipA u s = 0 := by
    have := LinearMap.congr_fun hzero ⟨s, hs⟩
    simpa using this
  rw [hsym, this, map_zero]

/- English proof (translation)
Introduce `A C I J _ _ _ _ _ ipA ip Θ pA pC RA RC T hsym _ hpos hRA hspan hmerge hsmul hRCA hli hex`. Rewrite using `[← LinearMap.range_eq_top]`. Assume the negation of the conclusion as `hne`. Take `⟨u, hu0, horth⟩` from `exists_ne_zero_orth ipA hsym _ hne`. Establish `horth' : ∀ y, ipA (Θ y) u = 0` using `fun y => horth _ (LinearMap.mem_range_self Θ y)`.

Take `⟨s, v, hv, hp, hus⟩` from `exists_sum_pairwise_unrelated pA RA hRA hmerge hsmul u (by rw [hspan]; exact Submodule.mem_top)`. Establish `hs : s.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce and unpack `rfl`. Conclude with `hu0 (by simpa using hus)`.

Establish `hx : ∀ i : s, ∃ x, (∀ y, ip y x = ipA (Θ y) (v i)) ∧ pC x (T i)` using `fun i => hex _ _ (hv i i.2)`. Use `choose x hx1 hx2 using hx`. Establish `hlin` using `hli s x (fun i => T i) hx2 (fun i i' hne hR => hp i i.2 i' i'.2 (fun h => hne (Subtype.ext h)) (hRCA _ _ hR))`. Establish `hzy : ∀ y, ip y (∑ i, x i) = 0`. Introduce `y`.

Rewrite using `[map_sum]`. Repeatedly rewrite using `[hx1]`. Rewrite using `[← map_sum, Finset.sum_coe_sort s v, ← hus, horth']`. Establish `hz : ∑ i, x i = 0`. Assume the negation of the conclusion as `h`.

Use `hpos _ h` as an intermediate fact. Rewrite `this` using `[hzy]`. Simplify using `at this`. Take `⟨i, hi⟩` from `hs`. Use `Fintype.linearIndependent_iff.mp hlin (fun _ => 1) (by simpa using hz) ⟨i, hi⟩` as an intermediate fact.

Conclude with `one_ne_zero this`.
-/
theorem surjective_of_adjoint_separates : ∀ (A C I J : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ A] (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (Θ : C →ₗ[ℂ] A) (pA : A → I → Prop) (pC : C → J → Prop) (RA : I → I → Prop) (RC : J → J → Prop) (T : I → J), (∀ x y, ipA x y = conj (ipA y x)) → (∀ x, x ≠ 0 → 0 < (ipA x x).re) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → Equivalence RA → Submodule.span ℂ {u | ∃ B, pA u B} = ⊤ → (∀ u u' B B' (a : ℂ), pA u B → pA u' B' → RA B B' → u + a • u' ≠ 0 → pA (u + a • u') B) → (∀ u B (a : ℂ), pA u B → a ≠ 0 → pA (a • u) B) → (∀ B B', RC (T B) (T B') → RA B B') → (∀ (ι : Type) (x : ι → C) (B : ι → J), (∀ i, pC (x i) (B i)) → (∀ i i', i ≠ i' → ¬ RC (B i) (B i')) → LinearIndependent ℂ x) → (∀ u B, pA u B → ∃ x, (∀ y, ip y x = ipA (Θ y) u) ∧ pC x (T B)) → Function.Surjective Θ := by
  intro A C I J _ _ _ _ _ ipA ip Θ pA pC RA RC T hsym _ hpos hRA hspan hmerge hsmul hRCA hli hex
  classical
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨u, hu0, horth⟩ := exists_ne_zero_orth ipA hsym _ hne
  have horth' : ∀ y, ipA (Θ y) u = 0 := fun y => horth _ (LinearMap.mem_range_self Θ y)
  obtain ⟨s, v, hv, hp, hus⟩ := exists_sum_pairwise_unrelated pA RA hRA hmerge hsmul u
    (by rw [hspan]; exact Submodule.mem_top)
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hu0 (by simpa using hus)
  have hx : ∀ i : s, ∃ x, (∀ y, ip y x = ipA (Θ y) (v i)) ∧ pC x (T i) :=
    fun i => hex _ _ (hv i i.2)
  choose x hx1 hx2 using hx
  have hlin := hli s x (fun i => T i) hx2
    (fun i i' hne hR => hp i i.2 i' i'.2 (fun h => hne (Subtype.ext h)) (hRCA _ _ hR))
  have hzy : ∀ y, ip y (∑ i, x i) = 0 := by
    intro y
    rw [map_sum]
    simp_rw [hx1]
    rw [← map_sum, Finset.sum_coe_sort s v, ← hus, horth']
  have hz : ∑ i, x i = 0 := by
    by_contra h
    have := hpos _ h
    rw [hzy] at this
    simp at this
  obtain ⟨i, hi⟩ := hs
  have := Fintype.linearIndependent_iff.mp hlin (fun _ => 1) (by simpa using hz) ⟨i, hi⟩
  exact one_ne_zero this

end GlobalTheory.ChainOnto
