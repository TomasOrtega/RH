import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

/- English proof (translation)
Establish `hcn : ∀ a, ∀ n ∈ N, c (a * n) = c a`. Introduce `a n hn`. Rewrite using `[hc, hN n hn, mul_zero, add_zero]`. Establish `hq : ∀ a b : Γ, (a : Γ ⧸ N) = b → c a = c b`. Introduce `a b h`.

Rewrite `h` using `[QuotientGroup.eq]`. Use `hcn a _ h` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Conclude with `this.symm`. Use `haveI : Fintype (Γ ⧸ N) := Fintype.ofFinite _`.

Establish `hcard : (Fintype.card (Γ ⧸ N) : k) = N.index`. Rewrite using `[Subgroup.index_eq_card, Nat.card_eq_fintype_card]`. Use `⟨-(N.index : k)⁻¹ * ∑ q : Γ ⧸ N, c q.out, fun s => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ q : Γ ⧸ N, (κ s : k) * c q.out = c (s • q).out - c s`. Introduce `q`.

Establish `: c (s * q.out) = c (s • q).out`. Apply `hq` to reduce the goal to its premises. Rewrite using `[QuotientGroup.out_eq']`. Use `conv_rhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression.

Rewrite using `[← this, hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∑ q : Γ ⧸ N, (κ s : k) * c q.out = ∑ q : Γ ⧸ N, c q.out - N.index * c s`. Repeatedly rewrite using `[h1]`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]`.

Use `congr 1`. Conclude with `Equiv.sum_comp (MulAction.toPerm s) (fun q : Γ ⧸ N => c q.out)`. Use `set S := ∑ q : Γ ⧸ N, c q.out`. Establish `hS : (κ s : k) * S = S - N.index * c s`. Rewrite using `[Finset.mul_sum]`.

Conclude with `key`. Establish `e : (κ s : k) * (-(N.index : k)⁻¹ * S) - -(N.index : k)⁻¹ * S = -(N.index : k)⁻¹ * ((κ s : k) * S - S)` using `by ring`. Rewrite using `[e, hS]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem cocycle_coboundary_of_vanishing_finite_index {k Γ : Type} [Field k] [Group Γ] (κ : Γ →* kˣ) (c : Γ → k)
    (hc : ∀ s t, c (s * t) = c s + (κ s : k) * c t) (N : Subgroup Γ) [N.FiniteIndex]
    (hN : ∀ n ∈ N, c n = 0) (hm : (N.index : k) ≠ 0) :
    ∃ X : k, ∀ s, c s = (κ s : k) * X - X := by
  have hcn : ∀ a, ∀ n ∈ N, c (a * n) = c a := by
    intro a n hn
    rw [hc, hN n hn, mul_zero, add_zero]
  have hq : ∀ a b : Γ, (a : Γ ⧸ N) = b → c a = c b := by
    intro a b h
    rw [QuotientGroup.eq] at h
    have := hcn a _ h
    rw [mul_inv_cancel_left] at this
    exact this.symm
  haveI : Fintype (Γ ⧸ N) := Fintype.ofFinite _
  have hcard : (Fintype.card (Γ ⧸ N) : k) = N.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  refine ⟨-(N.index : k)⁻¹ * ∑ q : Γ ⧸ N, c q.out, fun s => ?_⟩
  have h1 : ∀ q : Γ ⧸ N, (κ s : k) * c q.out = c (s • q).out - c s := by
    intro q
    have : c (s * q.out) = c (s • q).out := by
      apply hq
      rw [QuotientGroup.out_eq']
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [← this, hc]
    ring
  have key : ∑ q : Γ ⧸ N, (κ s : k) * c q.out = ∑ q : Γ ⧸ N, c q.out - N.index * c s := by
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    congr 1
    exact Equiv.sum_comp (MulAction.toPerm s) (fun q : Γ ⧸ N => c q.out)
  set S := ∑ q : Γ ⧸ N, c q.out
  have hS : (κ s : k) * S = S - N.index * c s := by
    rw [Finset.mul_sum]
    exact key
  have e : (κ s : k) * (-(N.index : k)⁻¹ * S) - -(N.index : k)⁻¹ * S
      = -(N.index : k)⁻¹ * ((κ s : k) * S - S) := by ring
  rw [e, hS]
  field_simp
  ring

/- English proof (translation)
Set `b` to `Basis.ofVectorSpace (ZMod l) (Kum.XDual 1 K₁ (ZMod l) (ZMod l))`. Set `cst` to `ZMod.castHom (dvd_refl l) k`. Set `e : _ → (K₁ → k)` to `fun i u => cst ((b i : K₁ → ZMod l) u)`. Establish `hT : ∀ x : Kum.XDual 1 K₁ (ZMod l) (ZMod l), (fun u => cst ((x : K₁ → ZMod l) u)) ∈ Submodule.span k (Set.range e)`. Introduce `x`.

Establish `hx : x ∈ Submodule.span (ZMod l) (Set.range b)`. Rewrite using `[b.span_eq]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨i, rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Consider the case `zero`. Use `Submodule.zero_mem (Submodule.span k (Set.range e)) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `u`.

Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`. Use `Submodule.add_mem _ hx hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `u`. Simplify using the standard rewrite rules.

Consider the case `smul a x _ hx`. Use `Submodule.smul_mem _ (cst a) hx using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `u`. Simplify using the standard rewrite rules. Establish `hsp : Kum.XDual 1 K₁ k k ≤ Submodule.span k (Set.range e)`.

Introduce `φ hφ`. Take `⟨hlc, hadd, hine, hdec⟩` from `hφ`. Use `haveI : CompactSpace K₁ := isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen K₁ hK).isCompact`. Establish `hfin : (Set.range φ).Finite` using `hlc.range_finite`. Use `letI : Module (ZMod l) k := Module.compHom k cst`.

Use `haveI : Module.Finite (ZMod l) (Submodule.span (ZMod l) (Set.range φ)) := Module.Finite.span_of_finite _ hfin`. Set `β` to `Module.finBasis (ZMod l) (Submodule.span (ZMod l) (Set.range φ))`. Establish `hmem : ∀ u, φ u ∈ Submodule.span (ZMod l) (Set.range φ)` using `fun u => Submodule.subset_span ⟨u, rfl⟩`. Set `ψ : Fin _ → (K₁ → ZMod l)` to `fun j u => β.coord j ⟨φ u, hmem u⟩`. Establish `hψ : ∀ j, ψ j ∈ Kum.XDual 1 K₁ (ZMod l) (ZMod l)`.

Introduce `j`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : IsLocallyConstant (fun u => (⟨φ u, hmem u⟩ : Submodule.span (ZMod l) (Set.range φ)))` using `(IsLocallyConstant.iff_eventually_eq _).mpr fun x => (hlc.eventually_eq x).mono fun y hy => Subtype.ext hy`. Conclude with `h0.comp (β.coord j)`. Introduce `a c show β.coord j ⟨φ (a * c), _⟩ = β.coord j ⟨φ a, _⟩ + β.coord j ⟨φ c, _⟩`.

Rewrite using `[← map_add]`. Use `congr 1`. Conclude with `Subtype.ext (hadd a c)`. Introduce `A u hu show β.coord j ⟨φ u, _⟩ = 0`. Rewrite using `[← map_zero (β.coord j)]`.

Use `congr 1`. Conclude with `Subtype.ext (hine A u hu)`. Introduce `A hA u hu show β.coord j ⟨φ u, _⟩ = 0`. Rewrite using `[← map_zero (β.coord j)]`. Use `congr 1`.

Conclude with `Subtype.ext (hdec A hA u hu)`. Establish `hrep : φ = ∑ j, (β j : k) • (fun u => cst (ψ j u))`. Use function extensionality and compare the values at `u`. Rewrite using `[Finset.sum_apply]`. Establish `h2 : ((∑ j, β.repr ⟨φ u, hmem u⟩ j • β j : Submodule.span (ZMod l) (Set.range φ)) : k) = φ u` using `congrArg Subtype.val (β.sum_repr ⟨φ u, hmem u⟩)`.

Rewrite using `[← h2, Submodule.coe_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[Submodule.coe_smul]`. Use `show cst _ * _ = _`.

Rewrite using `[mul_comm]`. Both sides reduce to the same expression. Rewrite using `[hrep]`. Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `j _`.

Apply `Submodule.smul_mem` to reduce the goal to its premises. Conclude with `hT ⟨ψ j, hψ j⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem rank_kummer_dual_le_clRk {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l]
    (K₁ : Subgroup (G F Ω)) (hK : IsOpen (K₁ : Set (G F Ω))) :
    Module.rank k (Kum.XDual 1 K₁ k k) ≤ clRk l K₁ := by
  classical
  let b := Basis.ofVectorSpace (ZMod l) (Kum.XDual 1 K₁ (ZMod l) (ZMod l))
  let cst := ZMod.castHom (dvd_refl l) k
  let e : _ → (K₁ → k) := fun i u => cst ((b i : K₁ → ZMod l) u)
  have hT : ∀ x : Kum.XDual 1 K₁ (ZMod l) (ZMod l),
      (fun u => cst ((x : K₁ → ZMod l) u)) ∈ Submodule.span k (Set.range e) := by
    intro x
    have hx : x ∈ Submodule.span (ZMod l) (Set.range b) := by
      rw [b.span_eq]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero =>
      convert Submodule.zero_mem (Submodule.span k (Set.range e)) using 1
      funext u
      simp
    | add x y _ _ hx hy =>
      convert Submodule.add_mem _ hx hy using 1
      funext u
      simp
    | smul a x _ hx =>
      convert Submodule.smul_mem _ (cst a) hx using 1
      funext u
      simp
  have hsp : Kum.XDual 1 K₁ k k ≤ Submodule.span k (Set.range e) := by
    intro φ hφ
    obtain ⟨hlc, hadd, hine, hdec⟩ := hφ
    haveI : CompactSpace K₁ :=
      isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen K₁ hK).isCompact
    have hfin : (Set.range φ).Finite := hlc.range_finite
    letI : Module (ZMod l) k := Module.compHom k cst
    haveI : Module.Finite (ZMod l) (Submodule.span (ZMod l) (Set.range φ)) :=
      Module.Finite.span_of_finite _ hfin
    let β := Module.finBasis (ZMod l) (Submodule.span (ZMod l) (Set.range φ))
    have hmem : ∀ u, φ u ∈ Submodule.span (ZMod l) (Set.range φ) :=
      fun u => Submodule.subset_span ⟨u, rfl⟩
    let ψ : Fin _ → (K₁ → ZMod l) := fun j u => β.coord j ⟨φ u, hmem u⟩
    have hψ : ∀ j, ψ j ∈ Kum.XDual 1 K₁ (ZMod l) (ZMod l) := by
      intro j
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h0 : IsLocallyConstant
            (fun u => (⟨φ u, hmem u⟩ : Submodule.span (ZMod l) (Set.range φ))) :=
          (IsLocallyConstant.iff_eventually_eq _).mpr
            fun x => (hlc.eventually_eq x).mono fun y hy => Subtype.ext hy
        exact h0.comp (β.coord j)
      · intro a c
        show β.coord j ⟨φ (a * c), _⟩ = β.coord j ⟨φ a, _⟩ + β.coord j ⟨φ c, _⟩
        rw [← map_add]
        congr 1
        exact Subtype.ext (hadd a c)
      · intro A u hu
        show β.coord j ⟨φ u, _⟩ = 0
        rw [← map_zero (β.coord j)]
        congr 1
        exact Subtype.ext (hine A u hu)
      · intro A hA u hu
        show β.coord j ⟨φ u, _⟩ = 0
        rw [← map_zero (β.coord j)]
        congr 1
        exact Subtype.ext (hdec A hA u hu)
    have hrep : φ = ∑ j, (β j : k) • (fun u => cst (ψ j u)) := by
      funext u
      rw [Finset.sum_apply]
      have h2 : ((∑ j, β.repr ⟨φ u, hmem u⟩ j • β j : Submodule.span (ZMod l) (Set.range φ)) : k)
          = φ u := congrArg Subtype.val (β.sum_repr ⟨φ u, hmem u⟩)
      rw [← h2, Submodule.coe_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Submodule.coe_smul]
      show cst _ * _ = _
      rw [mul_comm]
      rfl
    rw [hrep]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact hT ⟨ψ j, hψ j⟩
  calc Module.rank k (Kum.XDual 1 K₁ k k)
      ≤ Module.rank k (Submodule.span k (Set.range e)) := Submodule.rank_mono hsp
    _ ≤ Cardinal.mk (Set.range e) := rank_span_le _
    _ ≤ Cardinal.mk _ := Cardinal.mk_range_le
    _ = clRk l K₁ := b.mk_eq_rank''

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ k _ _ U K₁ _ hKU hK₁ hl Γ _ _ π hπc hπs V _ Gv _ _ loc κ hκ hIne`. Establish `hρ : ∀ (s : Γ) (w : k), chRep κ s w = (κ s : k) * w` using `fun _ _ => rfl`. Set `Zs` to `Z1C loc (chRep κ) (fun _ : V => (⊥ : Submodule k k))`. Set `Bs` to `Submodule.comap Zs.subtype (continuousCoboundaries1 (chRep κ) (fun _ : V => (⊥ : Submodule k k)))`. Establish `hc1 : ∀ z : Zs, ∀ s t, z.1.1 (s * t) = z.1.1 s + (κ s : k) * z.1.1 t`.

Introduce `z s t`. Take `⟨_, h2, _⟩` from `z.2`. Rewrite using `[h2 s t, hρ]`. Establish `hcl : ∀ z : Zs, ∀ v s, z.1.1 (loc v s) = (κ (loc v s) : k) * z.1.2 v - z.1.2 v`. Introduce `z v s`.

Take `⟨_, _, h3⟩` from `z.2`. Use `h3 v s` as an intermediate fact. Rewrite `this` using `[Submodule.mem_bot, sub_eq_zero, hρ]`. Conclude with `this`. Set `Φ : Zs →ₗ[k] (K₁ → k)` to `{ toFun := fun z u => z.1.1 (π ⟨u.1, hKU u.2⟩) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`.

Establish `hΦB : Bs ≤ LinearMap.ker Φ`. Introduce `z hz`. Take `⟨X, hX1, _⟩` from `hz`. Rewrite using `[LinearMap.mem_ker]`. Use function extensionality and compare the values at `u`.

Use `show z.1.1 (π ⟨u.1, hKU u.2⟩) = 0`. Use `(hX1 _).trans ?_` and prove the remaining obligations. Rewrite using `[hρ, hκ ⟨u.1, hKU u.2⟩ u.2, Units.val_one, one_mul, sub_self]`. Set `Φb` to `Bs.liftQ Φ hΦB`. Establish `hrange : LinearMap.range Φb ≤ Kum.XDual 1 K₁ k k`.

Rewrite using `[Submodule.range_liftQ]`. Introduce and unpack `_ ⟨z, rfl⟩`. Take `⟨hlcz, _, _⟩` from `z.2`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hcont : Continuous fun u : K₁ => π ⟨u.1, hKU u.2⟩` using `hπc.comp (Continuous.subtype_mk continuous_subtype_val _)`.

Conclude with `hlcz.comp_continuous hcont`. Introduce `a b show z.1.1 (π ⟨(a * b).1, hKU (a * b).2⟩) = z.1.1 (π ⟨a.1, hKU a.2⟩) + z.1.1 (π ⟨b.1, hKU b.2⟩)`. Establish `e : π ⟨(a * b).1, hKU (a * b).2⟩ = π ⟨a.1, hKU a.2⟩ * π ⟨b.1, hKU b.2⟩`. Rewrite using `[← map_mul]`. Both sides reduce to the same expression.

Rewrite using `[e, hc1, hκ _ a.2, Units.val_one, one_mul]`. Introduce `A u hu show z.1.1 (π ⟨u.1, hKU u.2⟩) = 0`. Establish `c1 : z.1.1 1 = 0` using `by simpa using hc1 z 1 1`. Establish `hk` using `hκ ⟨u.1, hKU u.2⟩ u.2`. Break down `hIne A ⟨u.1, hKU u.2⟩ hu u.2 with h | ⟨v, s, g, h⟩` into its components or cases.

Rewrite using `[h, c1]`. Rewrite `hk`, the goal using `[h]`. Simplify using `only [map_mul, map_inv, mul_inv_cancel_comm] at hk`. Establish `ch : z.1.1 (loc v s) = 0`. Rewrite using `[hcl z v s, hk, Units.val_one, one_mul, sub_self]`.

Establish `e3` using `hc1 z g g⁻¹`. Rewrite `e3` using `[mul_inv_cancel, c1]`. Rewrite using `[hc1, hc1, ch, map_mul, hk, mul_one, mul_zero, add_zero]`. Conclude with `e3.symm`. Introduce `A hA`.

It suffices to derive a contradiction. Simplify using `at hA`. Set `e0 : ({v // ∀ s, κ (loc v s) = 1} → k) → V → k` to `fun y v => if h : ∀ s, κ (loc v s) = 1 then y ⟨v, h⟩ else 0`. Establish `e0add : ∀ y y', e0 (y + y') = e0 y + e0 y'`. Introduce `y y'`.

Use function extensionality and compare the values at `v`. Apply the tactic sequence `by_cases h : ∀ s, κ (loc v s) = 1 <;> simp [e0, h]`. Establish `e0smul : ∀ (r : k) y, e0 (r • y) = r • e0 y`. Introduce `r y`. Use function extensionality and compare the values at `v`.

Apply the tactic sequence `by_cases h : ∀ s, κ (loc v s) = 1 <;> simp [e0, h]`. Establish `e0mem : ∀ y, (((0 : Γ → k), e0 y) : (Γ → k) × (V → k)) ∈ Zs`. Introduce `y`. Use `⟨IsLocallyConstant.const (0 : k), ?_, ?_⟩` and prove the remaining obligations. Introduce `s t show (0 : k) = 0 + chRep κ s 0`.

Simplify using the standard rewrite rules. Introduce `v s`. Rewrite using `[Submodule.mem_bot]`. Use `show (0 : k) - (chRep κ (loc v s) (e0 y v) - e0 y v) = 0`. Rewrite using `[hρ]`.

Distinguish the cases in `h : ∀ s, κ (loc v s) = 1`. Rewrite using `[h s, Units.val_one, one_mul, sub_self, sub_zero]`. Rewrite using `[show e0 y v = 0 from dif_neg h, mul_zero, sub_zero, sub_zero]`. Set `ι : ({v // ∀ s, κ (loc v s) = 1} → k) →ₗ[k] Zs` to `{ toFun := fun y => ⟨((0 : Γ → k), e0 y), e0mem y⟩ map_add' := fun y y' => Subtype.ext (Prod.ext (by simp) (e0add y y')) map_smul' := fun r y => Subtype.ext (Prod.ext (by simp) (e0smul r y)) }`. Set `ψ` to `Bs.mkQ ∘ₗ ι`.

Establish `hker : LinearMap.ker Φb ≤ LinearMap.range ψ`. Introduce `q hq`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective Bs q`. Rewrite `hq` using `[LinearMap.mem_ker, Submodule.liftQ_apply]`. Establish `hc0 : ∀ u : K₁, z.1.1 (π ⟨u.1, hKU u.2⟩) = 0` using `fun u => congrFun hq u`.

Use `set N := (K₁.subgroupOf U).map π with hNdef`. Establish `hdvd : N.index ∣ K₁.relIndex U` using `Subgroup.index_map_dvd _ hπs`. Establish `hNl : ¬ l ∣ N.index` using `fun h => hl (h.trans hdvd)`. Establish `hN0 : N.index ≠ 0` using `fun h => hNl (h ▸ dvd_zero l)`. Use `haveI : N.FiniteIndex := ⟨hN0⟩`.

Establish `hNk : (N.index : k) ≠ 0`. Rewrite using `[Ne, CharP.cast_eq_zero_iff k l]`. Conclude with `hNl`. Establish `hNc : ∀ n ∈ N, z.1.1 n = 0`. Introduce and unpack `_ ⟨u, hu, rfl⟩`.

Conclude with `hc0 ⟨u.1, Subgroup.mem_subgroupOf.mp hu⟩`. Take `⟨X, hX⟩` from `cocycle_coboundary_of_vanishing_finite_index κ z.1.1 (hc1 z) N hNc hNk`. Use `⟨fun v => z.1.2 v.1 - X, ?_⟩` and prove the remaining obligations. Use `show Bs.mkQ (ι _) = Bs.mkQ z`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`.

Use `⟨-X, ?_, ?_⟩` and prove the remaining obligations. Introduce `s show (0 : k) - z.1.1 s = chRep κ s (-X) - -X`. Rewrite using `[hρ, hX s]`. Expand and normalize the polynomial expressions, which then agree. Introduce `v`.

Rewrite using `[Submodule.mem_bot]`. Use `show e0 (fun v => z.1.2 v.1 - X) v - z.1.2 v - -X = 0`. Distinguish the cases in `h : ∀ s, κ (loc v s) = 1`. Rewrite using `[show e0 (fun v => z.1.2 v.1 - X) v = z.1.2 v - X from dif_pos h]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h` using `[show e0 (fun v => z.1.2 v.1 - X) v = 0 from dif_neg h] push_neg`. Take `⟨s, hs⟩` from `h`. Establish `e` using `hcl z v s`. Rewrite `e` using `[hX]`. Establish `hs' : (κ (loc v s) : k) ≠ 1` using `by rwa [Ne, Units.val_eq_one]`.

Establish `hm : ((κ (loc v s) : k) - 1) * (z.1.2 v - X) = 0` using `by linear_combination -e`. Break down `mul_eq_zero.mp hm with h1 | h1` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h1) hs'`. Take the linear combination `-h1`. Establish `h1 : Module.rank k (LinearMap.range Φb) ≤ Cardinal.lift.{0} (clRk l K₁)`.

Rewrite using `[Cardinal.lift_id]`. Conclude with `(Submodule.rank_mono hrange).trans (rank_kummer_dual_le_clRk l k K₁ hK₁)`. Establish `h2 : Module.rank k (LinearMap.ker Φb) ≤ (Nat.card {v // ∀ s, κ (loc v s) = 1} : Cardinal)`. Use `(Submodule.rank_mono hker).trans ((rank_range_le ψ).trans_eq ?_)` and prove the remaining obligations. Rewrite using `[rank_fun', Nat.card_eq_fintype_card]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.GC.strGen :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (U K₁ : Subgroup (G F Ω)) [K₁.Normal], K₁ ≤ U → IsOpen (K₁ : Set (G F Ω)) → ¬ l ∣ K₁.relIndex U → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] (π : U →* Γ), Continuous π → Function.Surjective π →
    ∀ (V : Type) [Fintype V] (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] (loc : ∀ v, Gv v →* Γ) (κ : Γ →* kˣ), (∀ u : U, u.1 ∈ K₁ → κ (π u) = 1) →
    (∀ A : ValuationSubring Ω, ∀ u : U, u.1 ∈ Ine (F := F) A → u.1 ∈ K₁ → π u = 1 ∨ ∃ v s g, π u = g * loc v s * g⁻¹) →
    Module.rank k (H1C loc (chRep κ) fun _ => ⊥) ≤ Cardinal.lift.{0} (clRk l K₁) + (Nat.card {v // ∀ s, κ (loc v s) = 1} : Cardinal) := by
  classical
  intro F Ω _ _ _ _ _ l _ k _ _ U K₁ _ hKU hK₁ hl Γ _ _ π hπc hπs V _ Gv _ _ loc κ hκ hIne
  have hρ : ∀ (s : Γ) (w : k), chRep κ s w = (κ s : k) * w := fun _ _ => rfl
  let Zs := Z1C loc (chRep κ) (fun _ : V => (⊥ : Submodule k k))
  let Bs := Submodule.comap Zs.subtype (continuousCoboundaries1 (chRep κ) (fun _ : V => (⊥ : Submodule k k)))
  have hc1 : ∀ z : Zs, ∀ s t, z.1.1 (s * t) = z.1.1 s + (κ s : k) * z.1.1 t := by
    intro z s t
    obtain ⟨_, h2, _⟩ := z.2
    rw [h2 s t, hρ]
  have hcl : ∀ z : Zs, ∀ v s, z.1.1 (loc v s) = (κ (loc v s) : k) * z.1.2 v - z.1.2 v := by
    intro z v s
    obtain ⟨_, _, h3⟩ := z.2
    have := h3 v s
    rw [Submodule.mem_bot, sub_eq_zero, hρ] at this
    exact this
  let Φ : Zs →ₗ[k] (K₁ → k) :=
    { toFun := fun z u => z.1.1 (π ⟨u.1, hKU u.2⟩)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΦB : Bs ≤ LinearMap.ker Φ := by
    intro z hz
    obtain ⟨X, hX1, _⟩ := hz
    rw [LinearMap.mem_ker]
    funext u
    show z.1.1 (π ⟨u.1, hKU u.2⟩) = 0
    refine (hX1 _).trans ?_
    rw [hρ, hκ ⟨u.1, hKU u.2⟩ u.2, Units.val_one, one_mul, sub_self]
  let Φb := Bs.liftQ Φ hΦB
  have hrange : LinearMap.range Φb ≤ Kum.XDual 1 K₁ k k := by
    rw [Submodule.range_liftQ]
    rintro _ ⟨z, rfl⟩
    obtain ⟨hlcz, _, _⟩ := z.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hcont : Continuous fun u : K₁ => π ⟨u.1, hKU u.2⟩ :=
        hπc.comp (Continuous.subtype_mk continuous_subtype_val _)
      exact hlcz.comp_continuous hcont
    · intro a b
      show z.1.1 (π ⟨(a * b).1, hKU (a * b).2⟩)
        = z.1.1 (π ⟨a.1, hKU a.2⟩) + z.1.1 (π ⟨b.1, hKU b.2⟩)
      have e : π ⟨(a * b).1, hKU (a * b).2⟩ = π ⟨a.1, hKU a.2⟩ * π ⟨b.1, hKU b.2⟩ := by
        rw [← map_mul]
        rfl
      rw [e, hc1, hκ _ a.2, Units.val_one, one_mul]
    · intro A u hu
      show z.1.1 (π ⟨u.1, hKU u.2⟩) = 0
      have c1 : z.1.1 1 = 0 := by simpa using hc1 z 1 1
      have hk := hκ ⟨u.1, hKU u.2⟩ u.2
      rcases hIne A ⟨u.1, hKU u.2⟩ hu u.2 with h | ⟨v, s, g, h⟩
      · rw [h, c1]
      · rw [h] at hk ⊢
        simp only [map_mul, map_inv, mul_inv_cancel_comm] at hk
        have ch : z.1.1 (loc v s) = 0 := by
          rw [hcl z v s, hk, Units.val_one, one_mul, sub_self]
        have e3 := hc1 z g g⁻¹
        rw [mul_inv_cancel, c1] at e3
        rw [hc1, hc1, ch, map_mul, hk, mul_one, mul_zero, add_zero]
        exact e3.symm
    · intro A hA
      exfalso
      simp at hA
  let e0 : ({v // ∀ s, κ (loc v s) = 1} → k) → V → k :=
    fun y v => if h : ∀ s, κ (loc v s) = 1 then y ⟨v, h⟩ else 0
  have e0add : ∀ y y', e0 (y + y') = e0 y + e0 y' := by
    intro y y'
    funext v
    by_cases h : ∀ s, κ (loc v s) = 1 <;> simp [e0, h]
  have e0smul : ∀ (r : k) y, e0 (r • y) = r • e0 y := by
    intro r y
    funext v
    by_cases h : ∀ s, κ (loc v s) = 1 <;> simp [e0, h]
  have e0mem : ∀ y, (((0 : Γ → k), e0 y) : (Γ → k) × (V → k)) ∈ Zs := by
    intro y
    refine ⟨IsLocallyConstant.const (0 : k), ?_, ?_⟩
    · intro s t
      show (0 : k) = 0 + chRep κ s 0
      simp
    · intro v s
      rw [Submodule.mem_bot]
      show (0 : k) - (chRep κ (loc v s) (e0 y v) - e0 y v) = 0
      rw [hρ]
      by_cases h : ∀ s, κ (loc v s) = 1
      · rw [h s, Units.val_one, one_mul, sub_self, sub_zero]
      · rw [show e0 y v = 0 from dif_neg h, mul_zero, sub_zero, sub_zero]
  let ι : ({v // ∀ s, κ (loc v s) = 1} → k) →ₗ[k] Zs :=
    { toFun := fun y => ⟨((0 : Γ → k), e0 y), e0mem y⟩
      map_add' := fun y y' => Subtype.ext (Prod.ext (by simp) (e0add y y'))
      map_smul' := fun r y => Subtype.ext (Prod.ext (by simp) (e0smul r y)) }
  let ψ := Bs.mkQ ∘ₗ ι
  have hker : LinearMap.ker Φb ≤ LinearMap.range ψ := by
    intro q hq
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective Bs q
    rw [LinearMap.mem_ker, Submodule.liftQ_apply] at hq
    have hc0 : ∀ u : K₁, z.1.1 (π ⟨u.1, hKU u.2⟩) = 0 := fun u => congrFun hq u
    set N := (K₁.subgroupOf U).map π with hNdef
    have hdvd : N.index ∣ K₁.relIndex U := Subgroup.index_map_dvd _ hπs
    have hNl : ¬ l ∣ N.index := fun h => hl (h.trans hdvd)
    have hN0 : N.index ≠ 0 := fun h => hNl (h ▸ dvd_zero l)
    haveI : N.FiniteIndex := ⟨hN0⟩
    have hNk : (N.index : k) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff k l]
      exact hNl
    have hNc : ∀ n ∈ N, z.1.1 n = 0 := by
      rintro _ ⟨u, hu, rfl⟩
      exact hc0 ⟨u.1, Subgroup.mem_subgroupOf.mp hu⟩
    obtain ⟨X, hX⟩ := cocycle_coboundary_of_vanishing_finite_index κ z.1.1 (hc1 z) N hNc hNk
    refine ⟨fun v => z.1.2 v.1 - X, ?_⟩
    show Bs.mkQ (ι _) = Bs.mkQ z
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨-X, ?_, ?_⟩
    · intro s
      show (0 : k) - z.1.1 s = chRep κ s (-X) - -X
      rw [hρ, hX s]
      ring
    · intro v
      rw [Submodule.mem_bot]
      show e0 (fun v => z.1.2 v.1 - X) v - z.1.2 v - -X = 0
      by_cases h : ∀ s, κ (loc v s) = 1
      · rw [show e0 (fun v => z.1.2 v.1 - X) v = z.1.2 v - X from dif_pos h]
        ring
      · rw [show e0 (fun v => z.1.2 v.1 - X) v = 0 from dif_neg h]
        push_neg at h
        obtain ⟨s, hs⟩ := h
        have e := hcl z v s
        rw [hX] at e
        have hs' : (κ (loc v s) : k) ≠ 1 := by rwa [Ne, Units.val_eq_one]
        have hm : ((κ (loc v s) : k) - 1) * (z.1.2 v - X) = 0 := by linear_combination -e
        rcases mul_eq_zero.mp hm with h1 | h1
        · exact absurd (sub_eq_zero.mp h1) hs'
        · linear_combination -h1
  have h1 : Module.rank k (LinearMap.range Φb) ≤ Cardinal.lift.{0} (clRk l K₁) := by
    rw [Cardinal.lift_id]
    exact (Submodule.rank_mono hrange).trans (rank_kummer_dual_le_clRk l k K₁ hK₁)
  have h2 : Module.rank k (LinearMap.ker Φb)
      ≤ (Nat.card {v // ∀ s, κ (loc v s) = 1} : Cardinal) := by
    refine (Submodule.rank_mono hker).trans ((rank_range_le ψ).trans_eq ?_)
    rw [rank_fun', Nat.card_eq_fintype_card]
  calc Module.rank k (H1C loc (chRep κ) fun _ => ⊥)
      = Module.rank k (LinearMap.range Φb) + Module.rank k (LinearMap.ker Φb) :=
        (LinearMap.rank_range_add_rank_ker Φb).symm
    _ ≤ _ := add_le_add h1 h2
