import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private def affPairs (N : Type) [AddCommGroup N] : Subgroup (Equiv.Perm N × Equiv.Perm N) where
  carrier := {p | ∀ x y, p.2 (x + y) = p.1 x + p.2 y}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb x y => by
    show a.2 (b.2 (x + y)) = a.1 (b.1 x) + a.2 (b.2 y)
    rw [hb, ha]
  inv_mem' := fun {a} ha x y => by
    show a.2.symm (x + y) = a.1.symm x + a.2.symm y
    apply a.2.injective
    rw [ha]
    simp

/- English proof (translation)
Introduce `D E E' _ _ _ _ _ _ I φ hcl hd q w' e hw' hI hq`. Establish `hn : 0 < orderOf e` using `orderOf_pos e`. Use `haveI : NeZero (orderOf e) := ⟨hn.ne'⟩`. Take `⟨d, hdl, hdI, hdφ⟩` from `hd (orderOf e) hn`. Set `f : Multiplicative (ZMod (orderOf e)) →* E` to `MonoidHom.mk' (fun x => e ^ (Multiplicative.toAdd x).val) (by`.

Introduce `a b`. Simplify using `only [toAdd_mul, ZMod.val_add, pow_mod_orderOf, pow_add])`. Establish `hf1 : f (Multiplicative.ofAdd 1) = e` using `by show e ^ (1 : ZMod (orderOf e)).val = e`. Rewrite using `[ZMod.val_one_eq_one_mod, pow_mod_orderOf, pow_one]`. Establish `hwl : IsLocallyConstant (f.comp d)` using `hdl.comp f`.

Establish `hwI : ∀ s ∈ I, (f.comp d) s = 1`. Introduce `s hs`. Simplify using `[hdI s hs]`. Use `⟨f.comp d, hwl, hwI, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : IsLocallyConstant (q.comp (f.comp d))` using `hwl.comp q`.

Establish `h2` using `(h1.prodMk hw').comp (fun p : E' × E' => p.1 = p.2)`. Establish `hclosed : IsClosed (((q.comp (f.comp d)).eqLocus w' : Subgroup D) : Set D)`. Use `h2.isClosed_fiber True` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Simplify using `[MonoidHom.eqLocus]`. Both sides reduce to the same expression. Establish `hle : I ⊔ Subgroup.zpowers φ ≤ (q.comp (f.comp d)).eqLocus w'`. Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce `s hs show q ((f.comp d) s) = w' s`.

Rewrite using `[hwI s hs, hI s hs, map_one]`. Rewrite using `[Subgroup.zpowers_le] show q (f (d φ)) = w' φ`. Rewrite using `[hdφ, hf1, hq]`. Use `Subgroup.topologicalClosure_minimal _ hle hclosed` as an intermediate fact. Rewrite `this` using `[hcl]`.

Use extensionality with `x`. Conclude with `this (Subgroup.mem_top x)`. Use `show f (d φ) = e`. Rewrite using `[hdφ, hf1]`. Introduce `g`.

Conclude with `Subgroup.npow_mem_zpowers e _`.
-/
private theorem zhat_lift :
    ∀ {D E E' : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group E] [Finite E] [Group E'] (I : Subgroup D) (φ : D),
      (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ →
      (∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) →
      ∀ (q : E →* E') (w' : D →* E') (e : E), IsLocallyConstant w' → (∀ s ∈ I, w' s = 1) → q e = w' φ →
      ∃ w : D →* E, IsLocallyConstant w ∧ (∀ s ∈ I, w s = 1) ∧ q.comp w = w' ∧ w φ = e ∧ ∀ g, w g ∈ Subgroup.zpowers e := by
  intro D E E' _ _ _ _ _ _ I φ hcl hd q w' e hw' hI hq
  have hn : 0 < orderOf e := orderOf_pos e
  haveI : NeZero (orderOf e) := ⟨hn.ne'⟩
  obtain ⟨d, hdl, hdI, hdφ⟩ := hd (orderOf e) hn
  let f : Multiplicative (ZMod (orderOf e)) →* E :=
    MonoidHom.mk' (fun x => e ^ (Multiplicative.toAdd x).val) (by
      intro a b
      simp only [toAdd_mul, ZMod.val_add, pow_mod_orderOf, pow_add])
  have hf1 : f (Multiplicative.ofAdd 1) = e := by
    show e ^ (1 : ZMod (orderOf e)).val = e
    rw [ZMod.val_one_eq_one_mod, pow_mod_orderOf, pow_one]
  have hwl : IsLocallyConstant (f.comp d) := hdl.comp f
  have hwI : ∀ s ∈ I, (f.comp d) s = 1 := by
    intro s hs
    simp [hdI s hs]
  refine ⟨f.comp d, hwl, hwI, ?_, ?_, ?_⟩
  · have h1 : IsLocallyConstant (q.comp (f.comp d)) := hwl.comp q
    have h2 := (h1.prodMk hw').comp (fun p : E' × E' => p.1 = p.2)
    have hclosed : IsClosed (((q.comp (f.comp d)).eqLocus w' : Subgroup D) : Set D) := by
      have := h2.isClosed_fiber True
      convert this using 1
      ext x
      simp [MonoidHom.eqLocus]
      rfl
    have hle : I ⊔ Subgroup.zpowers φ ≤ (q.comp (f.comp d)).eqLocus w' := by
      refine sup_le ?_ ?_
      · intro s hs
        show q ((f.comp d) s) = w' s
        rw [hwI s hs, hI s hs, map_one]
      · rw [Subgroup.zpowers_le]
        show q (f (d φ)) = w' φ
        rw [hdφ, hf1, hq]
    have := Subgroup.topologicalClosure_minimal _ hle hclosed
    rw [hcl] at this
    ext x
    exact this (Subgroup.mem_top x)
  · show f (d φ) = e
    rw [hdφ, hf1]
  · intro g
    exact Subgroup.npow_mem_zpowers e _

/- English proof (translation)
Introduce `k D M _ _ _ _ _ _ _ _ _ ρ I W hρ hI ⟨φ, hcl, hd⟩ hW`. Use `set N : Submodule k M := H0 (ρ.comp I.subtype : Representation k I M) with hNdef`. Establish `hN : ∀ m, m ∈ N ↔ ∀ s ∈ I, ρ s m = m` using `fun m => ⟨fun h s hs => h ⟨s, hs⟩, fun h s => h s.1 s.2⟩`. Establish `hev : ∀ y ∈ W, y φ ∈ N`. Introduce `y hy`.

Take `⟨⟨-, hc⟩, h0⟩` from `(hW y).1 hy`. Rewrite using `[hN]`. Introduce `s hs`. Establish `h1` using `hc s φ`. Establish `h2` using `hc φ (φ⁻¹ * s * φ)`.

Rewrite `h2` using `[h0 _ (hI.conj_mem' s hs φ), map_zero, add_zero]`. Rewrite `h1` using `[h0 s hs, zero_add]`. Rewrite using `[← h1, ← h2]`. Use `congr 1`. Use `group`.

Set `ev : W →ₗ[k] N` to `((LinearMap.proj φ).comp W.subtype).codRestrict N (fun y => hev y.1 y.2)`. Establish `hinj : Function.Injective ev`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Establish `hyφ : y.1 φ = 0` using `congrArg Subtype.val hy`.

Take `⟨⟨hcont, hc⟩, h0⟩` from `(hW y.1).1 y.2`. Establish `h1 : y.1 1 = 0` using `h0 1 I.one_mem`. Set `Z : Subgroup D` to `{ carrier := {g | y.1 g = 0} one_mem' := h1 mul_mem' := fun {a b} ha hb => by show y.1 (a * b) = 0`. Rewrite using `[hc, show y.1 a = 0 from ha, show y.1 b = 0 from hb, map_zero, add_zero]`. Use the proof step `inv_mem' := fun {a} ha => by`.

Use `hc a⁻¹ a` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel, h1, show y.1 a = 0 from ha, map_zero, add_zero]`. Conclude with `this.symm }`. Establish `hZ : IsClosed (Z : Set D)` using `isClosed_eq hcont continuous_const`. Establish `hle : I ⊔ Subgroup.zpowers φ ≤ Z` using `sup_le h0 (by rw [Subgroup.zpowers_le]; exact hyφ)`.

Use `Subgroup.topologicalClosure_minimal _ hle hZ` as an intermediate fact. Rewrite `this` using `[hcl]`. Use extensionality with `g`. Conclude with `this (Subgroup.mem_top g)`. Establish `hst : ∀ g : D, ∀ m : N, ρ g m ∈ N`.

Introduce `g m`. Rewrite using `[hN]`. Introduce `s hs`. Establish `h` using `(hN m).1 m.2 _ (hI.conj_mem' s hs g)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]`. Use `congr 2`. Use `group`. Use `_ = ρ g m := by rw [h]`. Set `a0 : D →* Function.End N` to `{ toFun := fun g m => ⟨ρ g m, hst g m⟩ map_one' := by`.

Use function extensionality and compare the values at `m`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ρ 1 m = m`. Simplify using the standard rewrite rules. Use the proof step `map_mul' := fun g h => by`.

Use function extensionality and compare the values at `m`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ρ (g * h) m = ρ g (ρ h m)`. Simplify using `}`. Set `a : D →* Equiv.Perm N` to `a0.toHomPerm`.

Establish `ha : ∀ g m, (a g m : M) = ρ g m` using `fun _ _ => rfl`. Establish `hal : IsLocallyConstant a`. Use `IsLocallyConstant.desc a (fun (p : Equiv.Perm N) (m : N) => (p m : M)) ?_ ?_` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_continuous]`. Conclude with `continuous_pi fun m => hρ.comp (continuous_id.prodMk continuous_const)`.

Introduce `p q h`. Use extensionality with `m`. Conclude with `congrFun h m`. Establish `haI : ∀ s ∈ I, a s = 1`. Introduce `s hs`.

Use extensionality with `m`. Conclude with `(hN m).1 m.2 s hs`. Establish `hsurj : Function.Surjective ev`. Introduce `m`. Take `⟨w, hwl, hwI, hq, hwφ, hw⟩` from `zhat_lift I φ hcl hd (MonoidHom.fst _ (Equiv.Perm N)) a (a φ, Equiv.addRight m * a φ) hal haI rfl`.

Establish `hP : ∀ g, w g ∈ affPairs N`. Introduce `g`. Use `(Subgroup.zpowers_le.2 ?_ : _ ≤ affPairs N) (hw g)` and prove the remaining obligations. Introduce `x y`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show ρ φ (x + y : M) + m = ρ φ x + (ρ φ y + m)`. Rewrite using `[map_add, add_assoc]`. Establish `hw1 : ∀ g, (w g).1 = a g` using `fun g => DFunLike.congr_fun hq g`. Use `⟨⟨fun g => ((w g).2 0 : M), (hW _).2 ⟨⟨?_, ?_⟩, ?_⟩⟩, ?_⟩` and prove the remaining obligations. Conclude with `(hwl.comp (fun p : Equiv.Perm N × Equiv.Perm N => (p.2 0 : M))).continuous`.

Introduce `g h`. Use `hP g ((w h).2 0) 0` as an intermediate fact. Rewrite `this` using `[add_zero, hw1]`. Use `show (((w (g * h)).2 0 : N) : M) = (w g).2 0 + ρ g ((w h).2 0)`. Rewrite using `[map_mul, Prod.snd_mul, Equiv.Perm.mul_apply, this, Submodule.coe_add, ha, add_comm]`.

Introduce `s hs show (((w s).2 0 : N) : M) = 0`. Rewrite using `[hwI s hs]`. Both sides reduce to the same expression. Apply `Subtype.ext show (((w φ).2 0 : N) : M) = m` to reduce the goal to its premises. Rewrite using `[hwφ]`.

Use `show ρ φ 0 + m = m`. Simplify using the standard rewrite rules. Conclude with `(LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩).finrank_eq`.
-/
theorem UpperTheory.finrank_unramified_cocycles_eq_finrank_invariants :
    ∀ {k D M : Type} [Field k] [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M) (I : Subgroup D) (W : Submodule k (D → M)), ContAction ρ → I.Normal → (∃ φ : D, (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧ ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) →
        (∀ y, y ∈ W ↔ y ∈ Z1 ρ ∧ ∀ s ∈ I, y s = 0) → finrank k W = finrank k (H0 (ρ.comp I.subtype : Representation k I M)) := by
  intro k D M _ _ _ _ _ _ _ _ _ ρ I W hρ hI ⟨φ, hcl, hd⟩ hW
  set N : Submodule k M := H0 (ρ.comp I.subtype : Representation k I M) with hNdef
  have hN : ∀ m, m ∈ N ↔ ∀ s ∈ I, ρ s m = m := fun m =>
    ⟨fun h s hs => h ⟨s, hs⟩, fun h s => h s.1 s.2⟩
  have hev : ∀ y ∈ W, y φ ∈ N := by
    intro y hy
    obtain ⟨⟨-, hc⟩, h0⟩ := (hW y).1 hy
    rw [hN]
    intro s hs
    have h1 := hc s φ
    have h2 := hc φ (φ⁻¹ * s * φ)
    rw [h0 _ (hI.conj_mem' s hs φ), map_zero, add_zero] at h2
    rw [h0 s hs, zero_add] at h1
    rw [← h1, ← h2]
    congr 1
    group
  let ev : W →ₗ[k] N := ((LinearMap.proj φ).comp W.subtype).codRestrict N (fun y => hev y.1 y.2)
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have hyφ : y.1 φ = 0 := congrArg Subtype.val hy
    obtain ⟨⟨hcont, hc⟩, h0⟩ := (hW y.1).1 y.2
    have h1 : y.1 1 = 0 := h0 1 I.one_mem
    let Z : Subgroup D :=
      { carrier := {g | y.1 g = 0}
        one_mem' := h1
        mul_mem' := fun {a b} ha hb => by
          show y.1 (a * b) = 0
          rw [hc, show y.1 a = 0 from ha, show y.1 b = 0 from hb, map_zero, add_zero]
        inv_mem' := fun {a} ha => by
          have := hc a⁻¹ a
          rw [inv_mul_cancel, h1, show y.1 a = 0 from ha, map_zero, add_zero] at this
          exact this.symm }
    have hZ : IsClosed (Z : Set D) := isClosed_eq hcont continuous_const
    have hle : I ⊔ Subgroup.zpowers φ ≤ Z := sup_le h0 (by rw [Subgroup.zpowers_le]; exact hyφ)
    have := Subgroup.topologicalClosure_minimal _ hle hZ
    rw [hcl] at this
    ext g
    exact this (Subgroup.mem_top g)
  have hst : ∀ g : D, ∀ m : N, ρ g m ∈ N := by
    intro g m
    rw [hN]
    intro s hs
    have h := (hN m).1 m.2 _ (hI.conj_mem' s hs g)
    calc ρ s (ρ g m) = ρ g (ρ (g⁻¹ * s * g) m) := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
          congr 2
          group
      _ = ρ g m := by rw [h]
  let a0 : D →* Function.End N :=
    { toFun := fun g m => ⟨ρ g m, hst g m⟩
      map_one' := by
        funext m
        apply Subtype.ext
        show ρ 1 m = m
        simp
      map_mul' := fun g h => by
        funext m
        apply Subtype.ext
        show ρ (g * h) m = ρ g (ρ h m)
        simp }
  let a : D →* Equiv.Perm N := a0.toHomPerm
  have ha : ∀ g m, (a g m : M) = ρ g m := fun _ _ => rfl
  have hal : IsLocallyConstant a := by
    refine IsLocallyConstant.desc a (fun (p : Equiv.Perm N) (m : N) => (p m : M)) ?_ ?_
    · rw [IsLocallyConstant.iff_continuous]
      exact continuous_pi fun m => hρ.comp (continuous_id.prodMk continuous_const)
    · intro p q h
      ext m
      exact congrFun h m
  have haI : ∀ s ∈ I, a s = 1 := by
    intro s hs
    ext m
    exact (hN m).1 m.2 s hs
  have hsurj : Function.Surjective ev := by
    intro m
    obtain ⟨w, hwl, hwI, hq, hwφ, hw⟩ := zhat_lift I φ hcl hd (MonoidHom.fst _ (Equiv.Perm N)) a
      (a φ, Equiv.addRight m * a φ) hal haI rfl
    have hP : ∀ g, w g ∈ affPairs N := by
      intro g
      refine (Subgroup.zpowers_le.2 ?_ : _ ≤ affPairs N) (hw g)
      intro x y
      apply Subtype.ext
      show ρ φ (x + y : M) + m = ρ φ x + (ρ φ y + m)
      rw [map_add, add_assoc]
    have hw1 : ∀ g, (w g).1 = a g := fun g => DFunLike.congr_fun hq g
    refine ⟨⟨fun g => ((w g).2 0 : M), (hW _).2 ⟨⟨?_, ?_⟩, ?_⟩⟩, ?_⟩
    · exact (hwl.comp (fun p : Equiv.Perm N × Equiv.Perm N => (p.2 0 : M))).continuous
    · intro g h
      have := hP g ((w h).2 0) 0
      rw [add_zero, hw1] at this
      show (((w (g * h)).2 0 : N) : M) = (w g).2 0 + ρ g ((w h).2 0)
      rw [map_mul, Prod.snd_mul, Equiv.Perm.mul_apply, this, Submodule.coe_add, ha, add_comm]
    · intro s hs
      show (((w s).2 0 : N) : M) = 0
      rw [hwI s hs]
      rfl
    · apply Subtype.ext
      show (((w φ).2 0 : N) : M) = m
      rw [hwφ]
      show ρ φ 0 + m = m
      simp
  exact (LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩).finrank_eq
