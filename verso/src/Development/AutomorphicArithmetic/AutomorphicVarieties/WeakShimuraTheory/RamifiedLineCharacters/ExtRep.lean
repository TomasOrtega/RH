import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def actM {A V J : Type} [CommRing A] [AddCommGroup V] [Module A V] (r t : A) (Y : J → V) :
    A × (J → V) →+ A × (J → V) where
  toFun u := (r * u.1, fun j => t • u.2 j + (r * u.1) • Y j)
  map_zero' := by ext <;> simp
  map_add' u v := by
    ext
    · simp [mul_add]
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, smul_add, add_smul]
      abel

private def mkRep {Γ M : Type} [Group Γ] [AddCommGroup M] (n : ℕ) [Module (ZMod n) M] (T : Γ → M →+ M) (h1 : ∀ u, T 1 u = u)
    (hm : ∀ g h u, T (g * h) u = T g (T h u)) : Representation (ZMod n) Γ M where
  toFun g := ((T g).toZModLinearMap n : Module.End (ZMod n) M)
  map_one' := LinearMap.ext h1
  map_mul' g h := LinearMap.ext (hm g h)

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun g => ?_` and prove the remaining obligations. Establish `ht : Filter.Tendsto (fun x => g⁻¹ * x) (nhds g) (nhds 1)`. Use `(continuous_mul_left g⁻¹).tendsto g` as an intermediate fact. Simplify using `using this`. Establish `hev : ∀ᶠ x in nhds g, f x = f g` using `by filter_upwards [ht hU] with x hx`.

Use `hf g _ hx` as an intermediate fact. Simplify using `using this`. Conclude with `tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)`.
-/
private theorem continuous_of_right_invariant_on_nhds_one {Γ X : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TopologicalSpace X] (U : Set Γ) (hU : U ∈ nhds (1 : Γ)) (f : Γ → X)
    (hf : ∀ g, ∀ h ∈ U, f (g * h) = f g) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have ht : Filter.Tendsto (fun x => g⁻¹ * x) (nhds g) (nhds 1) := by
    have := (continuous_mul_left g⁻¹).tendsto g
    simpa using this
  have hev : ∀ᶠ x in nhds g, f x = f g := by
    filter_upwards [ht hU] with x hx
    have := hf g _ hx
    simpa using this
  exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)

/- English proof (translation)
Introduce `O Γ k _ _ _ _ _ _ Φ a l _ _ ha hχ w w' J _ y hy`. Establish `hlp : (l ^ 1 : ℕ) = l` using `pow_one l`. Establish `hA : ∀ (v : ℤ × ℤ) g, a ↑(Φ.rt v g) = (a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 1 g))⁻¹) ^ v.1 * (a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 2 g))⁻¹) ^ v.2`. Introduce `v g`. Establish `e : ∀ u : Oˣ, a ↑u = ((Units.map a.toMonoidHom u : kˣ) : k)` using `fun u => rfl`.

Rewrite using `[e, e, e, e]`. Simplify using `only [Fr.rt, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_zpow, map_inv, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val]`. Establish `hsplit : ∀ g, a ↑(Φ.rt (w + w') g) = a ↑(Φ.rt w g) * a ↑(Φ.rt w' g)`. Introduce `g`. Rewrite using `[hA, hA, hA]`.

Simplify using `only [Prod.fst_add, Prod.snd_add]`. Establish `h0 : a ↑(Φ.χ 0 g) ≠ 0` using `((Φ.χ 0 g).isUnit.map a).ne_zero`. Establish `h1 : a ↑(Φ.χ 1 g) ≠ 0` using `((Φ.χ 1 g).isUnit.map a).ne_zero`. Establish `h2 : a ↑(Φ.χ 2 g) ≠ 0` using `((Φ.χ 2 g).isUnit.map a).ne_zero`. Establish `n1 : a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 1 g))⁻¹ ≠ 0` using `mul_ne_zero h0 (inv_ne_zero h1)`.

Establish `n2 : a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 2 g))⁻¹ ≠ 0` using `mul_ne_zero h0 (inv_ne_zero h2)`. Rewrite using `[zpow_add₀ n1, zpow_add₀ n2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hy1 : ∀ j, y j 1 = 0`. Introduce `j`.

Use `(hy j).coc 1 1` as an intermediate fact. Simplify using `only [mul_one, map_one, Units.val_one] at this`. Take the linear combination `-this`. Establish `hY : (⋃ j, Set.range (y j)).Finite` using `Set.finite_iUnion fun j => (hy j).lc.range_finite`. Set `A : Subring k` to `a.range`.

Use `haveI : Finite A := Set.Finite.to_subtype (s := (a.range : Set k)) (by rw [RingHom.coe_range]; exact ha)`. Set `V : Submodule A k` to `Submodule.span A (⋃ j, Set.range (y j))`. Use `haveI : Module.Finite A V := Module.Finite.span_of_finite A hY`. Use `haveI : Finite V := Module.finite_of_finite A`. Use `haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`.

Establish `hchar : ∀ x : k, (l ^ 1) • x = 0`. Introduce `x`. Rewrite using `[nsmul_eq_mul, hlp, CharP.cast_eq_zero, zero_mul]`. Use `letI iM : Module (ZMod (l ^ 1)) (A × (J → V)) := AddCommGroup.zmodModule (fun x => by`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(((l ^ 1) • x.1 : A) : k) = 0`. Rewrite using `[AddSubmonoidClass.coe_nsmul]`. Conclude with `hchar _`. Use function extensionality and compare the values at `j`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(((l ^ 1) • x.2 j : V) : k) = 0`. Rewrite using `[AddSubmonoidClass.coe_nsmul]`. Conclude with `hchar _)`. Use `letI : TopologicalSpace (A × (J → V)) := ⊥`.

Use `haveI : DiscreteTopology (A × (J → V)) := ⟨rfl⟩`. Set `rr : Γ → A` to `fun g => ⟨a ↑(Φ.rt w g), a.mem_range_self _⟩`. Set `tt : Γ → A` to `fun g => ⟨a ↑(Φ.rt (w + w') g), a.mem_range_self _⟩`. Set `YY : Γ → J → V` to `fun g j => ⟨y j g, Submodule.subset_span (Set.mem_iUnion.2 ⟨j, g, rfl⟩)⟩`. Set `T : Γ → (A × (J → V)) →+ (A × (J → V))` to `fun g => actM (rr g) (tt g) (YY g)`.

Establish `cs : ∀ (c : A) (v : V), ((c • v : V) : k) = (c : k) * (v : k)` using `fun c v => rfl`. Establish `h1 : ∀ u, T 1 u = u`. Introduce `u`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Apply `Subtype.ext show a ↑(Φ.rt w 1) * (u.1 : k) = u.1` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Use function extensionality and compare the values at `j`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((tt 1 • u.2 j + (rr 1 * u.1) • YY 1 j : V) : k) = u.2 j`. Rewrite using `[Submodule.coe_add, cs, cs]`.

Use `show a ↑(Φ.rt (w + w') 1) * (u.2 j : k) + (a ↑(Φ.rt w 1) * (u.1 : k)) * y j 1 = u.2 j`. Simplify using `[hy1]`. Establish `hm : ∀ g h u, T (g * h) u = T g (T h u)`. Introduce `g h u`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Apply `Subtype.ext show a ↑(Φ.rt w (g * h)) * (u.1 : k) = a ↑(Φ.rt w g) * (a ↑(Φ.rt w h) * (u.1 : k))` to reduce the goal to its premises. Rewrite using `[map_mul, Units.val_mul, map_mul, mul_assoc]`. Use function extensionality and compare the values at `j`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((tt (g * h) • u.2 j + (rr (g * h) * u.1) • YY (g * h) j : V) : k) = ((tt g • (tt h • u.2 j + (rr h * u.1) • YY h j) + (rr g * (rr h * u.1)) • YY g j : V) : k)`.

Rewrite using `[Submodule.coe_add, cs, cs, Submodule.coe_add, cs, cs, Submodule.coe_add, cs, cs]`. Use `show a ↑(Φ.rt (w + w') (g * h)) * (u.2 j : k) + (a ↑(Φ.rt w (g * h)) * (u.1 : k)) * y j (g * h) = a ↑(Φ.rt (w + w') g) * (a ↑(Φ.rt (w + w') h) * (u.2 j : k) + (a ↑(Φ.rt w h) * (u.1 : k)) * y j h) + (a ↑(Φ.rt w g) * (a ↑(Φ.rt w h) * (u.1 : k))) * y j g`. Rewrite using `[(hy j).coc g h, map_mul (Φ.rt (w + w')), map_mul (Φ.rt w), Units.val_mul, Units.val_mul, map_mul a, map_mul a, hsplit g, hsplit h]`. Expand and normalize the polynomial expressions, which then agree. Set `ρ : Representation (ZMod (l ^ 1)) Γ (A × (J → V))` to `mkRep (l ^ 1) T h1 hm`.

Establish `hker : ∀ g, (∀ i, a (Φ.χ i g) = 1) → (∀ j, y j g = 0) → ∀ u, T g u = u`. Introduce `g hg hyg`. Establish `hr : ∀ v : ℤ × ℤ, a ↑(Φ.rt v g) = 1`. Introduce `v`. Rewrite using `[hA, hg 0, hg 1, hg 2]`.

Simplify using the standard rewrite rules. Introduce `u`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Apply `Subtype.ext show a ↑(Φ.rt w g) * (u.1 : k) = u.1` to reduce the goal to its premises. Rewrite using `[hr, one_mul]`.

Use function extensionality and compare the values at `j`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((tt g • u.2 j + (rr g * u.1) • YY g j : V) : k) = u.2 j`. Rewrite using `[Submodule.coe_add, cs, cs]`. Use `show a ↑(Φ.rt (w + w') g) * (u.2 j : k) + (a ↑(Φ.rt w g) * (u.1 : k)) * y j g = u.2 j`.

Rewrite using `[hr, hr, hyg]`. Expand and normalize the polynomial expressions, which then agree. Set `p : (A × (J → V)) →+ k` to `{ toFun := fun u => (u.1 : k), map_zero' := rfl, map_add' := fun _ _ => rfl }`. Set `q : J → (A × (J → V)) →+ k` to `fun j => { toFun := fun u => (u.2 j : k), map_zero' := rfl, map_add' := fun _ _ => rfl }`. Set `m0 : A × (J → V)` to `(1, 0)`.

Use `⟨A × (J → V), inferInstance, iM, inferInstance, ⊥, ⟨rfl⟩, ρ, p, q, m0, ?_, fun g hg hyg => LinearMap.ext (hker g hg hyg), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `ReciprocityTheory.Gal.ContAction`. Rewrite using `[continuous_prod_of_discrete_right]`. Introduce `m`. Set `U : Set Γ` to `(⋂ i, (fun g => a (Φ.χ i g)) ⁻¹' {1}) ∩ ⋂ j, y j ⁻¹' {0}`.

Establish `hU : U ∈ nhds (1 : Γ)`. Apply `IsOpen.mem_nhds` to reduce the goal to its premises. Conclude with `(isOpen_iInter_of_finite fun i => (hχ i).isOpen_fiber 1).inter (isOpen_iInter_of_finite fun j => (hy j).lc.isOpen_fiber 0)`. Use `⟨Set.mem_iInter.2 fun i => ?_, Set.mem_iInter.2 fun j => ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Conclude with `hy1 j`. Apply `continuous_of_right_invariant_on_nhds_one U hU` to reduce the goal to its premises. Introduce `g h hh`. Establish `hh1 : ∀ i, a (Φ.χ i h) = 1` using `fun i => Set.mem_iInter.1 hh.1 i`. Establish `hh2 : ∀ j, y j h = 0` using `fun j => Set.mem_iInter.1 hh.2 j`.

Use `show T (g * h) m = T g m`. Rewrite using `[hm, hker h hh1 hh2 m]`. Introduce `g u`. Both sides reduce to the same expression. Introduce `j g u show ((tt g • u.2 j + (rr g * u.1) • YY g j : V) : k) = _`.

Rewrite using `[Submodule.coe_add, cs, cs]`. Use `show a ↑(Φ.rt (w + w') g) * (u.2 j : k) + (a ↑(Φ.rt w g) * (u.1 : k)) * y j g = a ↑(Φ.rt (w + w') g) * (u.2 j : k) + y j g * a ↑(Φ.rt w g) * (u.1 : k)`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`. Use `congrArg (fun u : A × (J → V) => (u.1 : k)) h` as an intermediate fact.

Simplify using `[m0] at this`. Introduce `u hu hne`. Rewrite `hu` using `[Submodule.mem_span_singleton]`. Take `⟨c, rfl⟩` from `hu`. Rewrite `hne`, the goal using `[← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]`.

Introduce `hp`. Apply `hne` to reduce the goal to its premises. Rewrite `hp` using `[map_nsmul]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `((c.val • (1 : A) : A) : k) = 0`. Rewrite using `[AddSubmonoidClass.coe_nsmul]`. Conclude with `hp`. Use function extensionality and compare the values at `j`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `((c.val • (0 : V) : V) : k) = 0`. Rewrite using `[smul_zero]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Ws.Gys.extRep :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k) (l : ℕ) [Fact l.Prime] [CharP k l], (Set.range a).Finite → (∀ i, IsLocallyConstant fun g => a (Φ.χ i g)) → ∀ (w w' : ℤ × ℤ) (J : Type) [Finite J] (y : J → Γ → k), (∀ j, Φ.Coc a w' (y j)) →
      ∃ (M : Type) (_ : AddCommGroup M) (_ : Module (ZMod (l ^ 1)) M) (_ : Finite M) (_ : TopologicalSpace M) (_ : DiscreteTopology M) (ρ : Representation (ZMod (l ^ 1)) Γ M)
        (p : M →+ k) (q : J → M →+ k) (m0 : M), ContAction ρ ∧ (∀ g, (∀ i, a (Φ.χ i g) = 1) → (∀ j, y j g = 0) → ρ g = 1) ∧
        (∀ g u, p (ρ g u) = a (Φ.rt w g) * p u) ∧ (∀ j g u, q j (ρ g u) = a (Φ.rt (w + w') g) * q j u + y j g * a (Φ.rt w g) * p u) ∧
        m0 ≠ 0 ∧ ∀ u ∈ Submodule.span (ZMod (l ^ 1)) {m0}, u ≠ 0 → p u ≠ 0 := by
  intro O Γ k _ _ _ _ _ _ Φ a l _ _ ha hχ w w' J _ y hy
  classical
  have hlp : (l ^ 1 : ℕ) = l := pow_one l
  have hA : ∀ (v : ℤ × ℤ) g, a ↑(Φ.rt v g) =
      (a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 1 g))⁻¹) ^ v.1 * (a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 2 g))⁻¹) ^ v.2 := by
    intro v g
    have e : ∀ u : Oˣ, a ↑u = ((Units.map a.toMonoidHom u : kˣ) : k) := fun u => rfl
    rw [e, e, e, e]
    simp only [Fr.rt, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_zpow, map_inv, Units.val_mul,
      Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val]
  have hsplit : ∀ g, a ↑(Φ.rt (w + w') g) = a ↑(Φ.rt w g) * a ↑(Φ.rt w' g) := by
    intro g
    rw [hA, hA, hA]
    simp only [Prod.fst_add, Prod.snd_add]
    have h0 : a ↑(Φ.χ 0 g) ≠ 0 := ((Φ.χ 0 g).isUnit.map a).ne_zero
    have h1 : a ↑(Φ.χ 1 g) ≠ 0 := ((Φ.χ 1 g).isUnit.map a).ne_zero
    have h2 : a ↑(Φ.χ 2 g) ≠ 0 := ((Φ.χ 2 g).isUnit.map a).ne_zero
    have n1 : a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 1 g))⁻¹ ≠ 0 := mul_ne_zero h0 (inv_ne_zero h1)
    have n2 : a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 2 g))⁻¹ ≠ 0 := mul_ne_zero h0 (inv_ne_zero h2)
    rw [zpow_add₀ n1, zpow_add₀ n2]
    ring
  have hy1 : ∀ j, y j 1 = 0 := by
    intro j
    have := (hy j).coc 1 1
    simp only [mul_one, map_one, Units.val_one] at this
    linear_combination -this
  have hY : (⋃ j, Set.range (y j)).Finite := Set.finite_iUnion fun j => (hy j).lc.range_finite
  let A : Subring k := a.range
  haveI : Finite A := Set.Finite.to_subtype (s := (a.range : Set k)) (by rw [RingHom.coe_range]; exact ha)
  let V : Submodule A k := Submodule.span A (⋃ j, Set.range (y j))
  haveI : Module.Finite A V := Module.Finite.span_of_finite A hY
  haveI : Finite V := Module.finite_of_finite A
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hchar : ∀ x : k, (l ^ 1) • x = 0 := by
    intro x
    rw [nsmul_eq_mul, hlp, CharP.cast_eq_zero, zero_mul]
  letI iM : Module (ZMod (l ^ 1)) (A × (J → V)) := AddCommGroup.zmodModule (fun x => by
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      change (((l ^ 1) • x.1 : A) : k) = 0
      rw [AddSubmonoidClass.coe_nsmul]
      exact hchar _
    · funext j
      apply Subtype.ext
      change (((l ^ 1) • x.2 j : V) : k) = 0
      rw [AddSubmonoidClass.coe_nsmul]
      exact hchar _)
  letI : TopologicalSpace (A × (J → V)) := ⊥
  haveI : DiscreteTopology (A × (J → V)) := ⟨rfl⟩
  let rr : Γ → A := fun g => ⟨a ↑(Φ.rt w g), a.mem_range_self _⟩
  let tt : Γ → A := fun g => ⟨a ↑(Φ.rt (w + w') g), a.mem_range_self _⟩
  let YY : Γ → J → V := fun g j => ⟨y j g, Submodule.subset_span (Set.mem_iUnion.2 ⟨j, g, rfl⟩)⟩
  let T : Γ → (A × (J → V)) →+ (A × (J → V)) := fun g => actM (rr g) (tt g) (YY g)
  have cs : ∀ (c : A) (v : V), ((c • v : V) : k) = (c : k) * (v : k) := fun c v => rfl
  have h1 : ∀ u, T 1 u = u := by
    intro u
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show a ↑(Φ.rt w 1) * (u.1 : k) = u.1
      simp
    · funext j
      apply Subtype.ext
      show ((tt 1 • u.2 j + (rr 1 * u.1) • YY 1 j : V) : k) = u.2 j
      rw [Submodule.coe_add, cs, cs]
      show a ↑(Φ.rt (w + w') 1) * (u.2 j : k) + (a ↑(Φ.rt w 1) * (u.1 : k)) * y j 1 = u.2 j
      simp [hy1]
  have hm : ∀ g h u, T (g * h) u = T g (T h u) := by
    intro g h u
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show a ↑(Φ.rt w (g * h)) * (u.1 : k) = a ↑(Φ.rt w g) * (a ↑(Φ.rt w h) * (u.1 : k))
      rw [map_mul, Units.val_mul, map_mul, mul_assoc]
    · funext j
      apply Subtype.ext
      show ((tt (g * h) • u.2 j + (rr (g * h) * u.1) • YY (g * h) j : V) : k) =
        ((tt g • (tt h • u.2 j + (rr h * u.1) • YY h j) + (rr g * (rr h * u.1)) • YY g j : V) : k)
      rw [Submodule.coe_add, cs, cs, Submodule.coe_add, cs, cs, Submodule.coe_add, cs, cs]
      show a ↑(Φ.rt (w + w') (g * h)) * (u.2 j : k) + (a ↑(Φ.rt w (g * h)) * (u.1 : k)) * y j (g * h) =
        a ↑(Φ.rt (w + w') g) * (a ↑(Φ.rt (w + w') h) * (u.2 j : k) + (a ↑(Φ.rt w h) * (u.1 : k)) * y j h) +
          (a ↑(Φ.rt w g) * (a ↑(Φ.rt w h) * (u.1 : k))) * y j g
      rw [(hy j).coc g h, map_mul (Φ.rt (w + w')), map_mul (Φ.rt w), Units.val_mul, Units.val_mul,
        map_mul a, map_mul a, hsplit g, hsplit h]
      ring
  let ρ : Representation (ZMod (l ^ 1)) Γ (A × (J → V)) := mkRep (l ^ 1) T h1 hm
  have hker : ∀ g, (∀ i, a (Φ.χ i g) = 1) → (∀ j, y j g = 0) → ∀ u, T g u = u := by
    intro g hg hyg
    have hr : ∀ v : ℤ × ℤ, a ↑(Φ.rt v g) = 1 := by
      intro v
      rw [hA, hg 0, hg 1, hg 2]
      simp
    intro u
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show a ↑(Φ.rt w g) * (u.1 : k) = u.1
      rw [hr, one_mul]
    · funext j
      apply Subtype.ext
      show ((tt g • u.2 j + (rr g * u.1) • YY g j : V) : k) = u.2 j
      rw [Submodule.coe_add, cs, cs]
      show a ↑(Φ.rt (w + w') g) * (u.2 j : k) + (a ↑(Φ.rt w g) * (u.1 : k)) * y j g = u.2 j
      rw [hr, hr, hyg]
      ring
  let p : (A × (J → V)) →+ k :=
    { toFun := fun u => (u.1 : k), map_zero' := rfl, map_add' := fun _ _ => rfl }
  let q : J → (A × (J → V)) →+ k := fun j =>
    { toFun := fun u => (u.2 j : k), map_zero' := rfl, map_add' := fun _ _ => rfl }
  let m0 : A × (J → V) := (1, 0)
  refine ⟨A × (J → V), inferInstance, iM, inferInstance, ⊥, ⟨rfl⟩, ρ, p, q, m0, ?_, fun g hg hyg => LinearMap.ext (hker g hg hyg), ?_, ?_, ?_, ?_⟩
  · unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    intro m
    let U : Set Γ := (⋂ i, (fun g => a (Φ.χ i g)) ⁻¹' {1}) ∩ ⋂ j, y j ⁻¹' {0}
    have hU : U ∈ nhds (1 : Γ) := by
      apply IsOpen.mem_nhds
      · exact (isOpen_iInter_of_finite fun i => (hχ i).isOpen_fiber 1).inter
          (isOpen_iInter_of_finite fun j => (hy j).lc.isOpen_fiber 0)
      · refine ⟨Set.mem_iInter.2 fun i => ?_, Set.mem_iInter.2 fun j => ?_⟩
        · simp
        · exact hy1 j
    apply continuous_of_right_invariant_on_nhds_one U hU
    intro g h hh
    have hh1 : ∀ i, a (Φ.χ i h) = 1 := fun i => Set.mem_iInter.1 hh.1 i
    have hh2 : ∀ j, y j h = 0 := fun j => Set.mem_iInter.1 hh.2 j
    show T (g * h) m = T g m
    rw [hm, hker h hh1 hh2 m]
  · intro g u
    rfl
  · intro j g u
    show ((tt g • u.2 j + (rr g * u.1) • YY g j : V) : k) = _
    rw [Submodule.coe_add, cs, cs]
    show a ↑(Φ.rt (w + w') g) * (u.2 j : k) + (a ↑(Φ.rt w g) * (u.1 : k)) * y j g =
      a ↑(Φ.rt (w + w') g) * (u.2 j : k) + y j g * a ↑(Φ.rt w g) * (u.1 : k)
    ring
  · intro h
    have := congrArg (fun u : A × (J → V) => (u.1 : k)) h
    simp [m0] at this
  · intro u hu hne
    rw [Submodule.mem_span_singleton] at hu
    obtain ⟨c, rfl⟩ := hu
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul] at hne ⊢
    intro hp
    apply hne
    rw [map_nsmul] at hp
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      change ((c.val • (1 : A) : A) : k) = 0
      rw [AddSubmonoidClass.coe_nsmul]
      exact hp
    · funext j
      apply Subtype.ext
      change ((c.val • (0 : V) : V) : k) = 0
      rw [smul_zero]
      rfl
