import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberDecomposition

open MulAction

/- English proof (translation)
Establish `h : a * s * a⁻¹ = (a * s * a⁻¹ * s⁻¹) * s` using `by group`. Rewrite using `[h]`. Conclude with `S.mul_mem (hc a s) hs`.
-/
private theorem conj_memS {G : Type} [Group G] {S : Subgroup G} (hc : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S)
    {s : G} (hs : s ∈ S) (a : G) : a * s * a⁻¹ ∈ S := by
  have h : a * s * a⁻¹ = (a * s * a⁻¹ * s⁻¹) * s := by group
  rw [h]
  exact S.mul_mem (hc a s) hs

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨s, hs⟩, rfl⟩`. Conclude with `⟨s, hs, rfl⟩`. Introduce and unpack `⟨s, hs, rfl⟩`. Conclude with `⟨⟨s, hs⟩, rfl⟩`.
-/
private theorem mem_orb {G : Type} [Group G] (S U : Subgroup G) (x : G) (y : G ⧸ U) :
    y ∈ orbit S (x : G ⧸ U) ↔ ∃ s ∈ S, y = ((s * x : G) : G ⧸ U) := by
  constructor
  · rintro ⟨⟨s, hs⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩

/- English proof (translation)
Use `haveI : S.Normal := ⟨fun n hn a => conj_memS hc hn a⟩`. Rewrite `hg` using `[← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul]`. Take `⟨s, hs, u, hu, rfl⟩` from `hg`. Take `⟨s₀, hs₀, rfl⟩` from `(mem_orb S U x y).1 hy`. Use `(mem_orb S U x _).2 ⟨s * (u * s₀ * x * u⁻¹ * x⁻¹), S.mul_mem hs ?_, ?_⟩` and prove the remaining obligations.

Use `S.mul_mem (conj_memS hc hs₀ u) (hc u x) using 1 group` and compare the differences between its conclusion and the goal. Rewrite using `[MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]`. Use `U.inv_mem hu using 1` and compare the differences between its conclusion and the goal. Use `group`.
-/
private theorem sup_act {G : Type} [Group G] {S U : Subgroup G} (hc : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S)
    {g : G} (hg : g ∈ S ⊔ U) (x : G) {y : G ⧸ U} (hy : y ∈ orbit S (x : G ⧸ U)) :
    g • y ∈ orbit S (x : G ⧸ U) := by
  haveI : S.Normal := ⟨fun n hn a => conj_memS hc hn a⟩
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hg
  obtain ⟨s, hs, u, hu, rfl⟩ := hg
  obtain ⟨s₀, hs₀, rfl⟩ := (mem_orb S U x y).1 hy
  refine (mem_orb S U x _).2 ⟨s * (u * s₀ * x * u⁻¹ * x⁻¹), S.mul_mem hs ?_, ?_⟩
  · convert S.mul_mem (conj_memS hc hs₀ u) (hc u x) using 1
    group
  · rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
    convert U.inv_mem hu using 1
    group

/- English proof (translation)
Take `⟨u, hu⟩` from `QuotientGroup.mk_out_eq_mul U g`. Rewrite using `[hu, hΦu _ u.2]`.
-/
private theorem phi_out {G : Type} [Group G] (U : Subgroup G) (Φ : G → ℂ) (hΦu : ∀ u ∈ U, ∀ g, Φ (g * u) = Φ g) (g : G) :
    Φ ((g : G ⧸ U).out) = Φ g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
  rw [hu, hΦu _ u.2]

/- English proof (translation)
Introduce `Γ G I _ _ _ ι S U' Γ₀ x Φ hc hN hΦl hΦu hT hdisj hcov`. Set `Γ' : Subgroup Γ` to `Subgroup.comap ι (S ⊔ U')`. Use `letI A : MulAction Γ (G ⧸ U') := MulAction.compHom _ ι`. Use `letI B : MulAction Γ' (G ⧸ U') := MulAction.compHom _ (ι.comp Γ'.subtype)`. Set `k : G ⧸ U' → ℂ` to `fun y => Φ y.out`.

Set `ki : I → G ⧸ U' → ℂ` to `fun i => (orbit S (x i : G ⧸ U')).indicator k`. Establish `hsmul : ∀ (h : Γ) (g : G), h • (g : G ⧸ U') = ((ι h * g : G) : G ⧸ U')` using `fun h g => rfl`. Establish `hk : ∀ g : G, k g = Φ g` using `phi_out U' Φ hΦu`. Establish `hkinv : ∀ (h : Γ) (y : G ⧸ U'), k (h • y) = k y`. Introduce `h y`.

Use `QuotientGroup.induction_on y fun g => ?_` and prove the remaining obligations. Rewrite using `[hsmul, hk, hk, hΦl]`. Establish `hki_mem : ∀ i y, ki i y ≠ 0 → y ∈ orbit S (x i : G ⧸ U')` using `fun i y h => Set.mem_of_indicator_ne_zero h`. Establish `hD` using `@UpperTheory.orbitalFiber_decomposition Γ (G ⧸ U') I _ A Γ₀ k (fun _ => Γ') (fun _ => G ⧸ U') (fun _ => inferInstance) (fun _ => B) (fun _ => Γ'.subtype) (fun _ => id) ki hN hkinv ?_ (fun _ _ _ => rfl) (fun _ => Function.injective_id) ?_ ?_ ?_ ?_`. Use `show UpperTheory.V.Z.Sym.gq Γ₀ k = ∑ i, UpperTheory.V.Z.Sym.gq (Γ₀.subgroupOf Γ') (ki i)`.

Rewrite using `[hD, finsum_eq_sum_of_fintype]`. Both sides reduce to the same expression. Take `⟨T, hT⟩` from `hT`. Use `⟨T.image (fun g : G => (g : G ⧸ U')), fun y => ?_⟩` and prove the remaining obligations. Use `QuotientGroup.induction_on y fun g _ => ?_` and prove the remaining obligations.

Take `⟨γ, s, hs, u, hu, rfl⟩` from `hT g`. Use `⟨γ, (s : G ⧸ U'), Finset.mem_image_of_mem _ hs, ?_⟩` and prove the remaining obligations. Rewrite using `[hsmul, QuotientGroup.eq]`. Use `U'.inv_mem hu using 1` and compare the differences between its conclusion and the goal. Use `group`.

Introduce `i h y`. Establish `hh : ι h ∈ S ⊔ U'` using `h.2`. Establish `e : h • y = (ι h) • y` using `rfl`. Establish `hmem : h • y ∈ orbit S (x i : G ⧸ U') ↔ y ∈ orbit S (x i : G ⧸ U')`. Rewrite using `[e]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy'`. Simplify using `using sup_act hc (Subgroup.inv_mem _ hh) (x i) hy'`. Introduce `hy`. Conclude with `sup_act hc hh (x i) hy`.

Use `show Set.indicator _ k (h • y) = Set.indicator _ k y`. Distinguish the cases in `hy : y ∈ orbit S (x i : G ⧸ U')`. Rewrite using `[Set.indicator_apply, Set.indicator_apply, if_pos (hmem.2 hy), if_pos hy]`. Conclude with `hkinv (h : Γ) y`. Rewrite using `[Set.indicator_apply, Set.indicator_apply, if_neg (mt hmem.1 hy), if_neg hy]`.

Introduce `i y h`. Conclude with `(Set.indicator_of_mem (hki_mem i y h) k).symm`. Introduce `z`. Use `QuotientGroup.induction_on z fun g hz => ?_` and prove the remaining obligations. Take `⟨i, γ, s, hs, u, hu, rfl⟩` from `hcov g`.

Establish `hy : ((s * x i : G) : G ⧸ U') ∈ orbit S (x i : G ⧸ U')` using `(mem_orb S U' _ _).2 ⟨s, hs, rfl⟩`. Establish `hval : k ((s * x i : G) : G ⧸ U') = k ((ι γ * s * x i * u : G) : G ⧸ U')`. Rewrite using `[hk, hk, hΦu _ hu, mul_assoc (ι γ) s, hΦl]`. Use `⟨i, ((s * x i : G) : G ⧸ U'), γ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show ki i _ = k _ from Set.indicator_of_mem hy k, hval]`.

Conclude with `hz`. Use `show _ = γ • ((s * x i : G) : G ⧸ U')`. Rewrite using `[hsmul, QuotientGroup.eq]`. Use `U'.inv_mem hu using 1` and compare the differences between its conclusion and the goal. Use `group`.

Introduce `i j y y' h hy hy' he`. Take `⟨s, hs, rfl⟩` from `(mem_orb S U' _ _).1 (hki_mem i y hy)`. Take `⟨s', hs', rfl⟩` from `(mem_orb S U' _ _).1 (hki_mem j y' hy')`. Express the relevant statement in the definitionally equal form `((ι h * (s * x i) : G) : G ⧸ U') = ((s' * x j : G) : G ⧸ U') at he`. Rewrite `he` using `[QuotientGroup.eq]`.

Take `⟨u, hu_mem, hu_eq⟩ : ∃ u ∈ U', (ι h * (s * x i))⁻¹ * (s' * x j) = u` from `⟨_, he, rfl⟩`. Establish `hxj : x j = ι h * ((ι h)⁻¹ * s'⁻¹ * ι h * s) * x i * u`. Rewrite using `[← hu_eq]`. Use `group`. Establish `e2 : ι h = s' * x j * u⁻¹ * (x i)⁻¹ * s⁻¹`.

Rewrite using `[← hu_eq]`. Use `group`. Establish `hmid : (ι h)⁻¹ * s'⁻¹ * ι h * s ∈ S` using `S.mul_mem (by simpa using conj_memS hc (S.inv_mem hs') (ι h)⁻¹) hs`. Establish `key : ∀ X : G, s' * X * u⁻¹ * X⁻¹ * s⁻¹ ∈ S ⊔ U'`. Introduce `X`.

Establish `e3 : s' * X * u⁻¹ * X⁻¹ * s⁻¹ = s' * (X * u⁻¹ * X⁻¹ * u⁻¹⁻¹) * u⁻¹ * s⁻¹` using `by group`. Rewrite using `[e3]`. Conclude with `Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hs') (Subgroup.mem_sup_left (hc _ _))) (Subgroup.mem_sup_right (U'.inv_mem hu_mem))) (Subgroup.mem_sup_left (S.inv_mem hs))`. Establish `hij` using `hdisj i j h _ hmid u hu_mem hxj`. Substitute `hij` using the available equality.

Use `⟨rfl, ⟨h, ?_⟩, rfl⟩` and prove the remaining obligations. Use `show ι h ∈ S ⊔ U'`. Rewrite using `[e2]`. Conclude with `key _`.
-/
theorem UpperTheory.orbitalFiber_sum_over_fibers :
    UpperTheory.V.Z.Sym.Glob.Fib.SumFib := by
  intro Γ G I _ _ _ ι S U' Γ₀ x Φ hc hN hΦl hΦu hT hdisj hcov
  classical
  let Γ' : Subgroup Γ := Subgroup.comap ι (S ⊔ U')
  letI A : MulAction Γ (G ⧸ U') := MulAction.compHom _ ι
  letI B : MulAction Γ' (G ⧸ U') := MulAction.compHom _ (ι.comp Γ'.subtype)
  let k : G ⧸ U' → ℂ := fun y => Φ y.out
  let ki : I → G ⧸ U' → ℂ := fun i => (orbit S (x i : G ⧸ U')).indicator k
  have hsmul : ∀ (h : Γ) (g : G), h • (g : G ⧸ U') = ((ι h * g : G) : G ⧸ U') := fun h g => rfl
  have hk : ∀ g : G, k g = Φ g := phi_out U' Φ hΦu
  have hkinv : ∀ (h : Γ) (y : G ⧸ U'), k (h • y) = k y := by
    intro h y
    refine QuotientGroup.induction_on y fun g => ?_
    rw [hsmul, hk, hk, hΦl]
  have hki_mem : ∀ i y, ki i y ≠ 0 → y ∈ orbit S (x i : G ⧸ U') :=
    fun i y h => Set.mem_of_indicator_ne_zero h
  have hD := @UpperTheory.orbitalFiber_decomposition Γ (G ⧸ U') I _ A Γ₀ k (fun _ => Γ') (fun _ => G ⧸ U')
    (fun _ => inferInstance) (fun _ => B) (fun _ => Γ'.subtype) (fun _ => id) ki hN hkinv
    ?_ (fun _ _ _ => rfl) (fun _ => Function.injective_id) ?_ ?_ ?_ ?_
  · show UpperTheory.V.Z.Sym.gq Γ₀ k = ∑ i, UpperTheory.V.Z.Sym.gq (Γ₀.subgroupOf Γ') (ki i)
    rw [hD, finsum_eq_sum_of_fintype]
    rfl
  · obtain ⟨T, hT⟩ := hT
    refine ⟨T.image (fun g : G => (g : G ⧸ U')), fun y => ?_⟩
    refine QuotientGroup.induction_on y fun g _ => ?_
    obtain ⟨γ, s, hs, u, hu, rfl⟩ := hT g
    refine ⟨γ, (s : G ⧸ U'), Finset.mem_image_of_mem _ hs, ?_⟩
    rw [hsmul, QuotientGroup.eq]
    convert U'.inv_mem hu using 1
    group
  · intro i h y
    have hh : ι h ∈ S ⊔ U' := h.2
    have e : h • y = (ι h) • y := rfl
    have hmem : h • y ∈ orbit S (x i : G ⧸ U') ↔ y ∈ orbit S (x i : G ⧸ U') := by
      rw [e]
      constructor
      · intro hy'
        simpa using sup_act hc (Subgroup.inv_mem _ hh) (x i) hy'
      · intro hy
        exact sup_act hc hh (x i) hy
    show Set.indicator _ k (h • y) = Set.indicator _ k y
    by_cases hy : y ∈ orbit S (x i : G ⧸ U')
    · rw [Set.indicator_apply, Set.indicator_apply, if_pos (hmem.2 hy), if_pos hy]
      exact hkinv (h : Γ) y
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg (mt hmem.1 hy), if_neg hy]
  · intro i y h
    exact (Set.indicator_of_mem (hki_mem i y h) k).symm
  · intro z
    refine QuotientGroup.induction_on z fun g hz => ?_
    obtain ⟨i, γ, s, hs, u, hu, rfl⟩ := hcov g
    have hy : ((s * x i : G) : G ⧸ U') ∈ orbit S (x i : G ⧸ U') := (mem_orb S U' _ _).2 ⟨s, hs, rfl⟩
    have hval : k ((s * x i : G) : G ⧸ U') = k ((ι γ * s * x i * u : G) : G ⧸ U') := by
      rw [hk, hk, hΦu _ hu, mul_assoc (ι γ) s, hΦl]
    refine ⟨i, ((s * x i : G) : G ⧸ U'), γ, ?_, ?_⟩
    · rw [show ki i _ = k _ from Set.indicator_of_mem hy k, hval]
      exact hz
    · show _ = γ • ((s * x i : G) : G ⧸ U')
      rw [hsmul, QuotientGroup.eq]
      convert U'.inv_mem hu using 1
      group
  · intro i j y y' h hy hy' he
    obtain ⟨s, hs, rfl⟩ := (mem_orb S U' _ _).1 (hki_mem i y hy)
    obtain ⟨s', hs', rfl⟩ := (mem_orb S U' _ _).1 (hki_mem j y' hy')
    change ((ι h * (s * x i) : G) : G ⧸ U') = ((s' * x j : G) : G ⧸ U') at he
    rw [QuotientGroup.eq] at he
    obtain ⟨u, hu_mem, hu_eq⟩ : ∃ u ∈ U', (ι h * (s * x i))⁻¹ * (s' * x j) = u := ⟨_, he, rfl⟩
    have hxj : x j = ι h * ((ι h)⁻¹ * s'⁻¹ * ι h * s) * x i * u := by
      rw [← hu_eq]
      group
    have e2 : ι h = s' * x j * u⁻¹ * (x i)⁻¹ * s⁻¹ := by
      rw [← hu_eq]
      group
    have hmid : (ι h)⁻¹ * s'⁻¹ * ι h * s ∈ S :=
      S.mul_mem (by simpa using conj_memS hc (S.inv_mem hs') (ι h)⁻¹) hs
    have key : ∀ X : G, s' * X * u⁻¹ * X⁻¹ * s⁻¹ ∈ S ⊔ U' := by
      intro X
      have e3 : s' * X * u⁻¹ * X⁻¹ * s⁻¹ = s' * (X * u⁻¹ * X⁻¹ * u⁻¹⁻¹) * u⁻¹ * s⁻¹ := by group
      rw [e3]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hs')
        (Subgroup.mem_sup_left (hc _ _))) (Subgroup.mem_sup_right (U'.inv_mem hu_mem)))
        (Subgroup.mem_sup_left (S.inv_mem hs))
    have hij := hdisj i j h _ hmid u hu_mem hxj
    subst hij
    refine ⟨rfl, ⟨h, ?_⟩, rfl⟩
    show ι h ∈ S ⊔ U'
    rw [e2]
    exact key _
