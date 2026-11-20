import Mathlib
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

/- English proof (translation)
Introduce `Γ _ K ι c hK hfin hidem horth`. Establish `hmk : ∀ v (g h : Γ), ((QuotientGroup.mk g : Γ ⧸ K.comap (c v)) = QuotientGroup.mk h) ↔ c v (g⁻¹ * h) ∈ K`. Introduce `v g h`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_comap]`. Establish `hle : ∀ v, K ≤ K.comap (c v)` using `fun v g hg => (hK g).1 hg v`.

Set `F : Γ ⧸ K → ∀ v, Γ ⧸ K.comap (c v)` to `fun q v => Quotient.liftOn' q (fun g => (QuotientGroup.mk g : Γ ⧸ K.comap (c v))) (by`. Introduce `a b hab`. Rewrite `hab` using `[QuotientGroup.leftRel_apply]`. Conclude with `(QuotientGroup.eq).2 (hle v hab))`. Establish `hF : ∀ g v, F (QuotientGroup.mk g) v = QuotientGroup.mk g` using `fun g v => rfl`.

Establish `hsupp : ∀ g, {w | F (QuotientGroup.mk g) w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))} = {v | c v g ∉ K}`. Introduce `g`. Use extensionality with `w`. Simplify using `only [Set.mem_setOf_eq, hF, ne_eq, hmk, mul_one, map_inv, inv_mem_iff]`. Set `G : Γ ⧸ K → {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite}` to `fun q => ⟨F q, by`.

Use `QuotientGroup.induction_on q ?_` and prove the remaining obligations. Introduce `g`. Rewrite using `[hsupp]`. Conclude with `hfin g⟩`. Establish `hinj : Function.Injective G`.

Introduce `q₁ q₂ h12`. Use `QuotientGroup.induction_on q₁ (fun g => ?_) h12` and prove the remaining obligations. Use `QuotientGroup.induction_on q₂ (fun k => ?_)` and prove the remaining obligations. Introduce `h12`. Establish `h' : ∀ v, F (QuotientGroup.mk g) v = F (QuotientGroup.mk k) v` using `fun v => congrFun (congrArg Subtype.val h12) v`.

Rewrite using `[QuotientGroup.eq, hK]`. Introduce `v`. Use `h' v` as an intermediate fact. Rewrite `this` using `[hF, hF, hmk]`. Conclude with `this`.

Establish `hcw : ∀ w (g : Γ), (QuotientGroup.mk (c w g) : Γ ⧸ K.comap (c w)) = QuotientGroup.mk g`. Introduce `w g`. Rewrite using `[hmk, map_mul, map_inv, hidem, inv_mul_cancel]`. Conclude with `K.one_mem`. Establish `hlist : ∀ (x : ι → Γ) (l : List ι), l.Nodup → ∀ w, c w ((l.map (fun v => c v (x v))).prod) = if w ∈ l then c w (x w) else 1`.

Introduce `x l`. Proceed by induction on `l with`. Consider the case `nil => intro _ w`. Simplify using the standard rewrite rules. Consider the case `cons a t ih`.

Introduce `hl w`. Rewrite `hl` using `[List.nodup_cons]`. Rewrite using `[List.map_cons, List.prod_cons, map_mul, ih hl.2]`. Distinguish the cases in `hw : w = a`. Substitute `hw` using the available equality.

Simplify using `[hidem, hl.1]`. Rewrite using `[horth a w _ (Ne.symm hw), one_mul]`. Simplify using `[hw]`. Establish `hsurj : Function.Surjective G`. Introduce and unpack `⟨f, hf⟩`.

Set `x : ι → Γ` to `fun v => (f v).out`. Use `⟨QuotientGroup.mk ((hf.toFinset.toList.map (fun v => c v (x v))).prod), ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `w`. Use `show F (QuotientGroup.mk _) w = f w`.

Rewrite using `[hF, ← hcw w, hlist x hf.toFinset.toList (Finset.nodup_toList _) w]`. Distinguish the cases in `hw : w ∈ hf.toFinset.toList`. Rewrite using `[if_pos hw, hcw]`. Conclude with `Quotient.out_eq (f w)`. Rewrite using `[if_neg hw]`.

Rewrite `hw` using `[Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not]`. Conclude with `hw.symm`. Conclude with `⟨Equiv.ofBijective G ⟨hinj, hsurj⟩, fun g v => rfl⟩`.
-/
theorem quotient_equiv_restrictedFamilies : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) (c : ι → Γ →* Γ), (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ g, {v | c v g ∉ K}.Finite) → (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) → ∃ e : Γ ⧸ K ≃ {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite}, ∀ (g : Γ) v, (e (QuotientGroup.mk g)).1 v = (QuotientGroup.mk g : Γ ⧸ K.comap (c v)) := by
  intro Γ _ K ι c hK hfin hidem horth
  classical
  have hmk : ∀ v (g h : Γ), ((QuotientGroup.mk g : Γ ⧸ K.comap (c v)) = QuotientGroup.mk h) ↔
      c v (g⁻¹ * h) ∈ K := by
    intro v g h
    rw [QuotientGroup.eq, Subgroup.mem_comap]
  have hle : ∀ v, K ≤ K.comap (c v) := fun v g hg => (hK g).1 hg v
  let F : Γ ⧸ K → ∀ v, Γ ⧸ K.comap (c v) := fun q v =>
    Quotient.liftOn' q (fun g => (QuotientGroup.mk g : Γ ⧸ K.comap (c v))) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab
      exact (QuotientGroup.eq).2 (hle v hab))
  have hF : ∀ g v, F (QuotientGroup.mk g) v = QuotientGroup.mk g := fun g v => rfl
  have hsupp : ∀ g, {w | F (QuotientGroup.mk g) w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))} =
      {v | c v g ∉ K} := by
    intro g
    ext w
    simp only [Set.mem_setOf_eq, hF, ne_eq, hmk, mul_one, map_inv, inv_mem_iff]
  let G : Γ ⧸ K → {f : ∀ v, Γ ⧸ K.comap (c v) //
      {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite} := fun q =>
    ⟨F q, by
      refine QuotientGroup.induction_on q ?_
      intro g
      rw [hsupp]
      exact hfin g⟩
  have hinj : Function.Injective G := by
    intro q₁ q₂ h12
    refine QuotientGroup.induction_on q₁ (fun g => ?_) h12
    refine QuotientGroup.induction_on q₂ (fun k => ?_)
    intro h12
    have h' : ∀ v, F (QuotientGroup.mk g) v = F (QuotientGroup.mk k) v :=
      fun v => congrFun (congrArg Subtype.val h12) v
    rw [QuotientGroup.eq, hK]
    intro v
    have := h' v
    rw [hF, hF, hmk] at this
    exact this
  have hcw : ∀ w (g : Γ), (QuotientGroup.mk (c w g) : Γ ⧸ K.comap (c w)) = QuotientGroup.mk g := by
    intro w g
    rw [hmk, map_mul, map_inv, hidem, inv_mul_cancel]
    exact K.one_mem
  have hlist : ∀ (x : ι → Γ) (l : List ι), l.Nodup → ∀ w,
      c w ((l.map (fun v => c v (x v))).prod) = if w ∈ l then c w (x w) else 1 := by
    intro x l
    induction l with
    | nil => intro _ w; simp
    | cons a t ih =>
      intro hl w
      rw [List.nodup_cons] at hl
      rw [List.map_cons, List.prod_cons, map_mul, ih hl.2]
      by_cases hw : w = a
      · subst hw
        simp [hidem, hl.1]
      · rw [horth a w _ (Ne.symm hw), one_mul]
        simp [hw]
  have hsurj : Function.Surjective G := by
    rintro ⟨f, hf⟩
    let x : ι → Γ := fun v => (f v).out
    refine ⟨QuotientGroup.mk ((hf.toFinset.toList.map (fun v => c v (x v))).prod), ?_⟩
    apply Subtype.ext
    funext w
    show F (QuotientGroup.mk _) w = f w
    rw [hF, ← hcw w, hlist x hf.toFinset.toList (Finset.nodup_toList _) w]
    by_cases hw : w ∈ hf.toFinset.toList
    · rw [if_pos hw, hcw]
      exact Quotient.out_eq (f w)
    · rw [if_neg hw]
      rw [Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
      exact hw.symm
  exact ⟨Equiv.ofBijective G ⟨hinj, hsurj⟩, fun g v => rfl⟩

end GlobalTheory
