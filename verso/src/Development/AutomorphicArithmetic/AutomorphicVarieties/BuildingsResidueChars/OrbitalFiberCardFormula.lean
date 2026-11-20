import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs

/- English proof (translation)
Introduce `G _ S U U' x Ux s₀ hS hU hx`. Establish `hmem : ∀ w : ↥(U' ⊓ S), (s₀ : G) * x * (w : G) * x⁻¹ ∈ S`. Introduce `w`. Establish `h1` using `S.mul_mem s₀.2 (hS.conj_mem (w : G) (Subgroup.mem_inf.1 w.2).2 x)`. Simplify `h1` using `[mul_assoc]`.

Set `g : ↥(U' ⊓ S) → ↥S ⧸ Ux` to `fun w => ((⟨_, hmem w⟩ : ↥S) : ↥S ⧸ Ux)`. Establish `hg : ∀ w w' : ↥(U' ⊓ S), g w = g w' ↔ (w : G)⁻¹ * (w' : G) ∈ U`. Introduce `w w'`. Simplify using `only [g]`. Rewrite using `[QuotientGroup.eq, hx]`.

Establish `e : x⁻¹ * (((⟨_, hmem w⟩ : ↥S)⁻¹ * ⟨_, hmem w'⟩ : ↥S) : G) * x = (w : G)⁻¹ * (w' : G)`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Use `group`. Rewrite using `[e]`. Establish `hgT : ∀ w, g w ∈ {s : ↥S ⧸ Ux | (((Quotient.out s : ↥S) : G) * x : G ⧸ U') = ((s₀ : G) * x : G ⧸ U')}`.

Introduce `w`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul Ux (⟨_, hmem w⟩ : ↥S)`. Simplify using `only [Set.mem_setOf_eq, g]`. Rewrite using `[hk, QuotientGroup.eq]`. Establish `hkU : x⁻¹ * ((k : ↥S) : G) * x ∈ U'` using `hU ((hx k).1 k.2)`.

Establish `e : ((((⟨_, hmem w⟩ : ↥S) * (k : ↥S) : ↥S) : G) * x)⁻¹ * ((s₀ : G) * x) = (x⁻¹ * ((k : ↥S) : G) * x)⁻¹ * ((w : G))⁻¹`. Simplify using `only [Subgroup.coe_mul]`. Use `group`. Rewrite using `[e]`. Conclude with `U'.mul_mem (U'.inv_mem hkU) (U'.inv_mem (Subgroup.mem_inf.1 w.2).1)`.

Rewrite using `[← Nat.card_coe_set_eq]`. Unfold `Subgroup.relIndex Subgroup.index`. Set `F : ↥(U' ⊓ S) ⧸ U.subgroupOf (U' ⊓ S) → {s : ↥S ⧸ Ux | (((Quotient.out s : ↥S) : G) * x : G ⧸ U') = ((s₀ : G) * x : G ⧸ U')}` to `Quotient.lift (fun w => ⟨g w, hgT w⟩) (fun a b hab => Subtype.ext ((hg a b).2 (by`. Establish `h` using `QuotientGroup.leftRel_apply.1 hab`. Simplify `h)))` using `[Subgroup.mem_subgroupOf]`.

Use `(Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)).symm` and prove the remaining obligations. Introduce `a b hab`. Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective a`. Take `⟨b, rfl⟩` from `QuotientGroup.mk_surjective b`. Establish `h` using `congrArg Subtype.val hab`.

Express the relevant statement in the definitionally equal form `g a = g b at h`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `using (hg a b).1 h`. Introduce and unpack `⟨s, hs⟩`. Rewrite `hs` using `[Set.mem_setOf_eq]`.

Establish `hwS : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x ∈ S`. Simplify using `using hS.conj_mem _ (S.mul_mem (S.inv_mem s₀.2) (Quotient.out s).2) x⁻¹`. Establish `hwU : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x ∈ U'`. Establish `h1` using `QuotientGroup.eq.1 hs`. Establish `e : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x = ((((Quotient.out s : ↥S) : G) * x)⁻¹ * ((s₀ : G) * x))⁻¹` using `by group`.

Rewrite using `[e]`. Conclude with `U'.inv_mem h1`. Use `⟨((⟨_, Subgroup.mem_inf.2 ⟨hwU, hwS⟩⟩ : ↥(U' ⊓ S)) : ↥(U' ⊓ S) ⧸ U.subgroupOf (U' ⊓ S)), Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g _ = s`. Use `conv_rhs => rw [← QuotientGroup.out_eq' s]`.

Simplify using `only [g]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only`. Use `group`.
-/
theorem UpperTheory.orbitalFiber_card_formula : UpperTheory.V.Z.Sym.Glob.Fib.CardFib := by
  intro G _ S U U' x Ux s₀ hS hU hx
  classical
  have hmem : ∀ w : ↥(U' ⊓ S), (s₀ : G) * x * (w : G) * x⁻¹ ∈ S := by
    intro w
    have h1 := S.mul_mem s₀.2 (hS.conj_mem (w : G) (Subgroup.mem_inf.1 w.2).2 x)
    simpa [mul_assoc] using h1
  let g : ↥(U' ⊓ S) → ↥S ⧸ Ux := fun w => ((⟨_, hmem w⟩ : ↥S) : ↥S ⧸ Ux)
  have hg : ∀ w w' : ↥(U' ⊓ S), g w = g w' ↔ (w : G)⁻¹ * (w' : G) ∈ U := by
    intro w w'
    simp only [g]
    rw [QuotientGroup.eq, hx]
    have e : x⁻¹ * (((⟨_, hmem w⟩ : ↥S)⁻¹ * ⟨_, hmem w'⟩ : ↥S) : G) * x = (w : G)⁻¹ * (w' : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
  have hgT : ∀ w, g w ∈ {s : ↥S ⧸ Ux | (((Quotient.out s : ↥S) : G) * x : G ⧸ U') = ((s₀ : G) * x : G ⧸ U')} := by
    intro w
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul Ux (⟨_, hmem w⟩ : ↥S)
    simp only [Set.mem_setOf_eq, g]
    rw [hk, QuotientGroup.eq]
    have hkU : x⁻¹ * ((k : ↥S) : G) * x ∈ U' := hU ((hx k).1 k.2)
    have e : ((((⟨_, hmem w⟩ : ↥S) * (k : ↥S) : ↥S) : G) * x)⁻¹ * ((s₀ : G) * x) =
        (x⁻¹ * ((k : ↥S) : G) * x)⁻¹ * ((w : G))⁻¹ := by
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    exact U'.mul_mem (U'.inv_mem hkU) (U'.inv_mem (Subgroup.mem_inf.1 w.2).1)
  rw [← Nat.card_coe_set_eq]
  unfold Subgroup.relIndex Subgroup.index
  let F : ↥(U' ⊓ S) ⧸ U.subgroupOf (U' ⊓ S) →
      {s : ↥S ⧸ Ux | (((Quotient.out s : ↥S) : G) * x : G ⧸ U') = ((s₀ : G) * x : G ⧸ U')} :=
    Quotient.lift (fun w => ⟨g w, hgT w⟩) (fun a b hab => Subtype.ext ((hg a b).2 (by
      have h := QuotientGroup.leftRel_apply.1 hab
      simpa [Subgroup.mem_subgroupOf] using h)))
  refine (Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)).symm
  · intro a b hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have h := congrArg Subtype.val hab
    change g a = g b at h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using (hg a b).1 h
  · rintro ⟨s, hs⟩
    rw [Set.mem_setOf_eq] at hs
    have hwS : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x ∈ S := by
      simpa using hS.conj_mem _ (S.mul_mem (S.inv_mem s₀.2) (Quotient.out s).2) x⁻¹
    have hwU : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x ∈ U' := by
      have h1 := QuotientGroup.eq.1 hs
      have e : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x =
          ((((Quotient.out s : ↥S) : G) * x)⁻¹ * ((s₀ : G) * x))⁻¹ := by
        group
      rw [e]
      exact U'.inv_mem h1
    refine ⟨((⟨_, Subgroup.mem_inf.2 ⟨hwU, hwS⟩⟩ : ↥(U' ⊓ S)) : ↥(U' ⊓ S) ⧸ U.subgroupOf (U' ⊓ S)),
      Subtype.ext ?_⟩
    change g _ = s
    conv_rhs => rw [← QuotientGroup.out_eq' s]
    simp only [g]
    congr 1
    apply Subtype.ext
    dsimp only
    group
