import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.UrCard

def affPairs (N : Type) [AddCommGroup N] : Subgroup (Equiv.Perm N × Equiv.Perm N) where
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
theorem zhat_lift :
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

variable {R D M : Type} [CommRing R] [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
  [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]

def invI (ρ : Representation R D M) (I : Subgroup D) : Submodule R M where
  carrier := {m | ∀ s ∈ I, ρ s m = m}
  zero_mem' := fun s _ => by simp
  add_mem' := fun {a b} ha hb s hs => by simp [map_add, ha s hs, hb s hs]
  smul_mem' := fun c a ha s hs => by simp [map_smul, ha s hs]

def vanI (ρ : Representation R D M) (I : Subgroup D) : Submodule R (D → M) where
  carrier := {y | y ∈ Z1 ρ ∧ ∀ s ∈ I, y s = 0}
  zero_mem' := ⟨(Z1 ρ).zero_mem, fun _ _ => rfl⟩
  add_mem' := fun {a b} ha hb => ⟨(Z1 ρ).add_mem ha.1 hb.1, fun s hs => by simp [ha.2 s hs, hb.2 s hs]⟩
  smul_mem' := fun c a ha => ⟨(Z1 ρ).smul_mem c ha.1, fun s hs => by simp [ha.2 s hs]⟩

end GlobalTheory.Ord2.UrCard

namespace GlobalTheory.Ord2.UrCard

variable {R D M : Type} [CommRing R] [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
  [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]

/- English proof (translation)
Use `set N : Submodule R M := invI ρ I with hNdef`. Establish `hN : ∀ m, m ∈ N ↔ ∀ s ∈ I, ρ s m = m` using `fun m => Iff.rfl`. Establish `hW : ∀ y, y ∈ vanI ρ I ↔ y ∈ Z1 ρ ∧ ∀ s ∈ I, y s = 0` using `fun y => Iff.rfl`. Establish `hev : ∀ y ∈ vanI ρ I, y φ ∈ N`. Introduce `y hy`.

Take `⟨⟨-, hc⟩, h0⟩` from `(hW y).1 hy`. Rewrite using `[hN]`. Introduce `s hs`. Establish `h1` using `hc s φ`. Establish `h2` using `hc φ (φ⁻¹ * s * φ)`.

Rewrite `h2` using `[h0 _ (hI.conj_mem' s hs φ), map_zero, add_zero]`. Rewrite `h1` using `[h0 s hs, zero_add]`. Rewrite using `[← h1, ← h2]`. Use `congr 1`. Use `group`.

Set `ev : vanI ρ I → N` to `fun y => ⟨y.1 φ, hev y.1 y.2⟩`. Establish `hinj : Function.Injective ev`. Introduce `y y' hyy`. Establish `hyφ : (y.1 - y'.1) φ = 0`. Use `congrArg Subtype.val hyy` as an intermediate fact.

Simplify using `only [ev] at this`. Simplify using `[this]`. Establish `hmem : y.1 - y'.1 ∈ vanI ρ I` using `(vanI ρ I).sub_mem y.2 y'.2`. Take `⟨⟨hcont, hc⟩, h0⟩` from `(hW _).1 hmem`. Use `set z := y.1 - y'.1 with hz`.

Establish `h1 : z 1 = 0` using `h0 1 I.one_mem`. Set `Z : Subgroup D` to `{ carrier := {g | z g = 0} one_mem' := h1 mul_mem' := fun {a b} ha hb => by show z (a * b) = 0`. Rewrite using `[hc, show z a = 0 from ha, show z b = 0 from hb, map_zero, add_zero]`. Use the proof step `inv_mem' := fun {a} ha => by`. Use `hc a⁻¹ a` as an intermediate fact.

Rewrite `this` using `[inv_mul_cancel, h1, show z a = 0 from ha, map_zero, add_zero]`. Conclude with `this.symm }`. Establish `hZ : IsClosed (Z : Set D)` using `isClosed_eq hcont continuous_const`. Establish `hle : I ⊔ Subgroup.zpowers φ ≤ Z` using `sup_le h0 (by rw [Subgroup.zpowers_le]; exact hyφ)`. Use `Subgroup.topologicalClosure_minimal _ hle hZ` as an intermediate fact.

Rewrite `this` using `[hcl]`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Establish `hg : z g = 0` using `this (Subgroup.mem_top g)`. Rewrite `hg` using `[hz, Pi.sub_apply, sub_eq_zero]`.

Conclude with `hg`. Establish `hst : ∀ g : D, ∀ m : N, ρ g m ∈ N`. Introduce `g m`. Rewrite using `[hN]`. Introduce `s hs`.

Establish `h` using `(hN m).1 m.2 _ (hI.conj_mem' s hs g)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]`. Use `congr 2`. Use `group`.

Use `_ = ρ g m := by rw [h]`. Set `a0 : D →* Function.End N` to `{ toFun := fun g m => ⟨ρ g m, hst g m⟩ map_one' := by`. Use function extensionality and compare the values at `m`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ρ 1 m = m`.

Simplify using the standard rewrite rules. Use the proof step `map_mul' := fun g h => by`. Use function extensionality and compare the values at `m`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ρ (g * h) m = ρ g (ρ h m)`.

Simplify using `}`. Set `a : D →* Equiv.Perm N` to `a0.toHomPerm`. Establish `ha : ∀ g m, (a g m : M) = ρ g m` using `fun _ _ => rfl`. Establish `hal : IsLocallyConstant a` using `by haveI : Finite N := inferInstance`. Use `IsLocallyConstant.desc a (fun (p : Equiv.Perm N) (m : N) => (p m : M)) ?_ ?_` and prove the remaining obligations.

Rewrite using `[IsLocallyConstant.iff_continuous]`. Conclude with `continuous_pi fun m => hρ.comp (continuous_id.prodMk continuous_const)`. Introduce `p q h`. Use extensionality with `m`. Conclude with `congrFun h m`.

Establish `haI : ∀ s ∈ I, a s = 1`. Introduce `s hs`. Use extensionality with `m`. Conclude with `(hN m).1 m.2 s hs`. Establish `hsurj : Function.Surjective ev`.

Introduce `m`. Take `⟨w, hwl, hwI, hq, hwφ, hw⟩` from `zhat_lift I φ hcl hd (MonoidHom.fst _ (Equiv.Perm N)) a (a φ, Equiv.addRight m * a φ) hal haI rfl`. Establish `hP : ∀ g, w g ∈ affPairs N`. Introduce `g`. Use `(Subgroup.zpowers_le.2 ?_ : _ ≤ affPairs N) (hw g)` and prove the remaining obligations.

Introduce `x y`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ρ φ (x + y : M) + m = ρ φ x + (ρ φ y + m)`. Rewrite using `[map_add, add_assoc]`. Establish `hw1 : ∀ g, (w g).1 = a g` using `fun g => DFunLike.congr_fun hq g`.

Use `⟨⟨fun g => ((w g).2 0 : M), (hW _).2 ⟨⟨?_, ?_⟩, ?_⟩⟩, ?_⟩` and prove the remaining obligations. Conclude with `(hwl.comp (fun p : Equiv.Perm N × Equiv.Perm N => (p.2 0 : M))).continuous`. Introduce `g h`. Use `hP g ((w h).2 0) 0` as an intermediate fact. Rewrite `this` using `[add_zero, hw1]`.

Use `show (((w (g * h)).2 0 : N) : M) = (w g).2 0 + ρ g ((w h).2 0)`. Rewrite using `[map_mul, Prod.snd_mul, Equiv.Perm.mul_apply, this, Submodule.coe_add, ha, add_comm]`. Introduce `s hs show (((w s).2 0 : N) : M) = 0`. Rewrite using `[hwI s hs]`. Both sides reduce to the same expression.

Apply `Subtype.ext show (((w φ).2 0 : N) : M) = m` to reduce the goal to its premises. Rewrite using `[hwφ]`. Use `show ρ φ 0 + m = m`. Simplify using the standard rewrite rules. Conclude with `Nat.card_congr (Equiv.ofBijective ev ⟨hinj, hsurj⟩)`.
-/
theorem card_vanI (ρ : Representation R D M) (I : Subgroup D) [hI : I.Normal] (hρ : ContAction ρ) (φ : D)
    (hcl : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) :
    Nat.card (vanI ρ I) = Nat.card (invI ρ I) := by
  set N : Submodule R M := invI ρ I with hNdef
  have hN : ∀ m, m ∈ N ↔ ∀ s ∈ I, ρ s m = m := fun m => Iff.rfl
  have hW : ∀ y, y ∈ vanI ρ I ↔ y ∈ Z1 ρ ∧ ∀ s ∈ I, y s = 0 := fun y => Iff.rfl
  have hev : ∀ y ∈ vanI ρ I, y φ ∈ N := by
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
  let ev : vanI ρ I → N := fun y => ⟨y.1 φ, hev y.1 y.2⟩
  have hinj : Function.Injective ev := by
    intro y y' hyy
    have hyφ : (y.1 - y'.1) φ = 0 := by
      have := congrArg Subtype.val hyy
      simp only [ev] at this
      simp [this]
    have hmem : y.1 - y'.1 ∈ vanI ρ I := (vanI ρ I).sub_mem y.2 y'.2
    obtain ⟨⟨hcont, hc⟩, h0⟩ := (hW _).1 hmem
    set z := y.1 - y'.1 with hz
    have h1 : z 1 = 0 := h0 1 I.one_mem
    let Z : Subgroup D :=
      { carrier := {g | z g = 0}
        one_mem' := h1
        mul_mem' := fun {a b} ha hb => by
          show z (a * b) = 0
          rw [hc, show z a = 0 from ha, show z b = 0 from hb, map_zero, add_zero]
        inv_mem' := fun {a} ha => by
          have := hc a⁻¹ a
          rw [inv_mul_cancel, h1, show z a = 0 from ha, map_zero, add_zero] at this
          exact this.symm }
    have hZ : IsClosed (Z : Set D) := isClosed_eq hcont continuous_const
    have hle : I ⊔ Subgroup.zpowers φ ≤ Z := sup_le h0 (by rw [Subgroup.zpowers_le]; exact hyφ)
    have := Subgroup.topologicalClosure_minimal _ hle hZ
    rw [hcl] at this
    apply Subtype.ext
    funext g
    have hg : z g = 0 := this (Subgroup.mem_top g)
    rw [hz, Pi.sub_apply, sub_eq_zero] at hg
    exact hg
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
    haveI : Finite N := inferInstance
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
  exact Nat.card_congr (Equiv.ofBijective ev ⟨hinj, hsurj⟩)

end GlobalTheory.Ord2.UrCard

namespace GlobalTheory.Ord2.UrCard

variable {R D M : Type} [CommRing R] [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
  [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]

/- English proof (translation)
Establish `hVZ : vanI ρ I ≤ Z1 ρ` using `fun y hy => hy.1`. Establish `hBZ : B1 ρ ≤ Z1 ρ` using `coboundaries_le_cocycles ρ hρ`. Use `set Q := (B1 ρ).comap (Z1 ρ).subtype with hQ`. Establish `hmem : ∀ y : vanI ρ I, Q.mkQ (Submodule.inclusion hVZ y) ∈ H1ur ρ I`. Introduce `y`.

Use `show resH1 ρ I.subtype continuous_subtype_val (Q.mkQ (Submodule.inclusion hVZ y)) = 0`. Rewrite using `[Submodule.mkQ_apply]`. Express the relevant statement in the definitionally equal form `Submodule.mapQ _ _ (restrictCocycles1 ρ I.subtype continuous_subtype_val) _ _ = 0`. Rewrite using `[Submodule.mapQ_apply]`. Establish `: restrictCocycles1 ρ I.subtype continuous_subtype_val (Submodule.inclusion hVZ y) = 0` using `Subtype.ext (funext fun s => y.2.2 s s.2)`.

Rewrite using `[this]`. Both sides reduce to the same expression. Set `f : vanI ρ I →ₗ[R] H1ur ρ I` to `LinearMap.codRestrict (H1ur ρ I) (Q.mkQ ∘ₗ Submodule.inclusion hVZ) hmem`. Establish `hf : ∀ y, ((f y : H1ur ρ I) : H1 ρ) = Q.mkQ (Submodule.inclusion hVZ y)` using `fun _ => rfl`. Establish `hfs : Function.Surjective f`.

Introduce and unpack `⟨x, hx⟩`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `hx' : resH1 ρ I.subtype continuous_subtype_val (Submodule.Quotient.mk z) = 0` using `hx`. Express the relevant statement in the definitionally equal form `Submodule.mapQ _ _ (restrictCocycles1 ρ I.subtype continuous_subtype_val) _ _ = 0 at hx'`. Rewrite `hx'` using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`.

Take `⟨m, hm⟩` from `(mem_coboundaries1 _ _).1 hx'`. Establish `hy : z.1 - d0 ρ m ∈ vanI ρ I`. Use `⟨(Z1 ρ).sub_mem z.2 (hBZ ⟨m, rfl⟩), fun s hs => ?_⟩` and prove the remaining obligations. Use `hm ⟨s, hs⟩` as an intermediate fact. Simplify using `only [Submodule.coe_subtype] at this`.

Simplify using `only [Pi.sub_apply, amitsur_d0_apply]`. Rewrite using `[sub_eq_zero]`. Conclude with `this`. Use `⟨⟨_, hy⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hf, Submodule.mkQ_apply]`.

Apply `(Submodule.Quotient.eq _).2` to reduce the goal to its premises. Use `show (z.1 - d0 ρ m) - z.1 ∈ B1 ρ`. Rewrite using `[sub_sub_cancel_left]`. Conclude with `(B1 ρ).neg_mem ⟨m, rfl⟩`. Establish `hker : ∀ y : vanI ρ I, y ∈ LinearMap.ker f ↔ y.1 ∈ B1 ρ`.

Introduce `y`. Rewrite using `[LinearMap.mem_ker, ← Subtype.coe_inj, hf, Submodule.mkQ_apply]`. Use `show Submodule.Quotient.mk _ = 0 ↔ _`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Both sides reduce to the same expression.

Establish `hgm : ∀ m : invI ρ I, d0 ρ m.1 ∈ vanI ρ I` using `fun m => ⟨hBZ ⟨m.1, rfl⟩, fun s hs => by simp [amitsur_d0_apply, m.2 s hs]⟩`. Set `g : invI ρ I →ₗ[R] vanI ρ I` to `LinearMap.codRestrict (vanI ρ I) ((d0 ρ) ∘ₗ (invI ρ I).subtype) hgm`. Establish `hrange : LinearMap.range g = LinearMap.ker f`. Use extensionality with `y`. Rewrite using `[hker, LinearMap.mem_range]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, rfl⟩`. Conclude with `⟨m.1, rfl⟩`. Introduce `hy`. Take `⟨m, hm⟩` from `(mem_coboundaries1 _ _).1 hy`.

Establish `hmI : m ∈ invI ρ I`. Introduce `s hs`. Establish `h1` using `hm s`. Rewrite `h1` using `[y.2.2 s hs, eq_comm, sub_eq_zero]`. Conclude with `h1`.

Use `⟨⟨m, hmI⟩, Subtype.ext (funext fun s => ?_)⟩` and prove the remaining obligations. Conclude with `(hm s).symm`. Establish `hkg : Nat.card (LinearMap.ker g) = Nat.card (H0 ρ)`. Use `Nat.card_congr { toFun := fun m => ⟨m.1.1, fun s => ?_⟩ invFun := fun m => ⟨⟨m.1, fun s _ => m.2 s⟩, ?_⟩ left_inv := fun m => rfl right_inv := fun m => rfl }` and prove the remaining obligations. Establish `h` using `congrArg (fun y : vanI ρ I => y.1 s) (LinearMap.mem_ker.1 m.2)`.

Establish `h' : ρ s m.1.1 - m.1.1 = 0` using `h`. Conclude with `sub_eq_zero.1 h'`. Rewrite using `[LinearMap.mem_ker]`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `s`.

Use `show ρ s m.1 - m.1 = 0`. Rewrite using `[m.2 s, sub_self]`. Establish `e1` using `(LinearMap.ker f).card_eq_card_quotient_mul_card`. Rewrite `e1` using `[Nat.card_congr (f.quotKerEquivOfSurjective hfs).toEquiv]`. Establish `e2` using `(LinearMap.ker g).card_eq_card_quotient_mul_card`.

Rewrite `e2` using `[Nat.card_congr (g.quotKerEquivRange).toEquiv, hkg, Nat.card_congr (LinearEquiv.ofEq _ _ hrange).toEquiv]`. Establish `e3` using `card_vanI ρ I hρ φ hcl hd`. Establish `hpos : Nat.card (invI ρ I) ≠ 0` using `Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩`. Rewrite `e3` using `[e1, e2]`. Rewrite `hpos` using `[e2]`.

Establish `hk : Nat.card (LinearMap.ker f) ≠ 0` using `fun h => hpos (by rw [h, mul_zero])`. Rewrite `e3` using `[mul_comm (Nat.card (H0 ρ))]`. Conclude with `Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) e3`.
-/
theorem card_H1ur (ρ : Representation R D M) (I : Subgroup D) [hI : I.Normal] (hρ : ContAction ρ) (φ : D)
    (hcl : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) :
    Nat.card (H1ur ρ I) = Nat.card (H0 ρ) := by
  have hVZ : vanI ρ I ≤ Z1 ρ := fun y hy => hy.1
  have hBZ : B1 ρ ≤ Z1 ρ := coboundaries_le_cocycles ρ hρ
  set Q := (B1 ρ).comap (Z1 ρ).subtype with hQ
  have hmem : ∀ y : vanI ρ I, Q.mkQ (Submodule.inclusion hVZ y) ∈ H1ur ρ I := by
    intro y
    show resH1 ρ I.subtype continuous_subtype_val (Q.mkQ (Submodule.inclusion hVZ y)) = 0
    rw [Submodule.mkQ_apply]
    change Submodule.mapQ _ _ (restrictCocycles1 ρ I.subtype continuous_subtype_val) _ _ = 0
    rw [Submodule.mapQ_apply]
    have : restrictCocycles1 ρ I.subtype continuous_subtype_val (Submodule.inclusion hVZ y) = 0 :=
      Subtype.ext (funext fun s => y.2.2 s s.2)
    rw [this]
    rfl
  let f : vanI ρ I →ₗ[R] H1ur ρ I :=
    LinearMap.codRestrict (H1ur ρ I) (Q.mkQ ∘ₗ Submodule.inclusion hVZ) hmem
  have hf : ∀ y, ((f y : H1ur ρ I) : H1 ρ) = Q.mkQ (Submodule.inclusion hVZ y) := fun _ => rfl
  have hfs : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : resH1 ρ I.subtype continuous_subtype_val (Submodule.Quotient.mk z) = 0 := hx
    change Submodule.mapQ _ _ (restrictCocycles1 ρ I.subtype continuous_subtype_val) _ _ = 0 at hx'
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx'
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hx'
    have hy : z.1 - d0 ρ m ∈ vanI ρ I := by
      refine ⟨(Z1 ρ).sub_mem z.2 (hBZ ⟨m, rfl⟩), fun s hs => ?_⟩
      have := hm ⟨s, hs⟩
      simp only [Submodule.coe_subtype] at this
      simp only [Pi.sub_apply, amitsur_d0_apply]
      rw [sub_eq_zero]
      exact this
    refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
    rw [hf, Submodule.mkQ_apply]
    apply (Submodule.Quotient.eq _).2
    show (z.1 - d0 ρ m) - z.1 ∈ B1 ρ
    rw [sub_sub_cancel_left]
    exact (B1 ρ).neg_mem ⟨m, rfl⟩
  have hker : ∀ y : vanI ρ I, y ∈ LinearMap.ker f ↔ y.1 ∈ B1 ρ := by
    intro y
    rw [LinearMap.mem_ker, ← Subtype.coe_inj, hf, Submodule.mkQ_apply]
    show Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    rfl
  have hgm : ∀ m : invI ρ I, d0 ρ m.1 ∈ vanI ρ I := fun m =>
    ⟨hBZ ⟨m.1, rfl⟩, fun s hs => by simp [amitsur_d0_apply, m.2 s hs]⟩
  let g : invI ρ I →ₗ[R] vanI ρ I := LinearMap.codRestrict (vanI ρ I) ((d0 ρ) ∘ₗ (invI ρ I).subtype) hgm
  have hrange : LinearMap.range g = LinearMap.ker f := by
    ext y
    rw [hker, LinearMap.mem_range]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m.1, rfl⟩
    · intro hy
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hy
      have hmI : m ∈ invI ρ I := by
        intro s hs
        have h1 := hm s
        rw [y.2.2 s hs, eq_comm, sub_eq_zero] at h1
        exact h1
      refine ⟨⟨m, hmI⟩, Subtype.ext (funext fun s => ?_)⟩
      exact (hm s).symm
  have hkg : Nat.card (LinearMap.ker g) = Nat.card (H0 ρ) := by
    refine Nat.card_congr
      { toFun := fun m => ⟨m.1.1, fun s => ?_⟩
        invFun := fun m => ⟨⟨m.1, fun s _ => m.2 s⟩, ?_⟩
        left_inv := fun m => rfl
        right_inv := fun m => rfl }
    · have h := congrArg (fun y : vanI ρ I => y.1 s) (LinearMap.mem_ker.1 m.2)
      have h' : ρ s m.1.1 - m.1.1 = 0 := h
      exact sub_eq_zero.1 h'
    · rw [LinearMap.mem_ker]
      apply Subtype.ext
      funext s
      show ρ s m.1 - m.1 = 0
      rw [m.2 s, sub_self]
  have e1 := (LinearMap.ker f).card_eq_card_quotient_mul_card
  rw [Nat.card_congr (f.quotKerEquivOfSurjective hfs).toEquiv] at e1
  have e2 := (LinearMap.ker g).card_eq_card_quotient_mul_card
  rw [Nat.card_congr (g.quotKerEquivRange).toEquiv, hkg,
    Nat.card_congr (LinearEquiv.ofEq _ _ hrange).toEquiv] at e2
  have e3 := card_vanI ρ I hρ φ hcl hd
  have hpos : Nat.card (invI ρ I) ≠ 0 := Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  rw [e1, e2] at e3
  rw [e2] at hpos
  have hk : Nat.card (LinearMap.ker f) ≠ 0 := fun h => hpos (by rw [h, mul_zero])
  rw [mul_comm (Nat.card (H0 ρ))] at e3
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) e3

end GlobalTheory.Ord2.UrCard

namespace GlobalTheory.Ord2.UrCard

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A v ρ hρ hv`. Take `⟨φ, -, hcl, hd⟩` from `UpperTheory.V.GC.decZhat F Ω v A hv`. Conclude with `card_H1ur ρ _ hρ φ hcl hd`.
-/
theorem card_unramified_h1_eq_card_h0 : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation (ZMod (l ^ r)) (Dec (F := F) A) M) (hρ : ContAction ρ), IsPlaceOver A v → Nat.card (H1ur ρ ((Ine (F := F) A).subgroupOf (Dec (F := F) A))) = Nat.card (H0 ρ) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A v ρ hρ hv
  obtain ⟨φ, -, hcl, hd⟩ := UpperTheory.V.GC.decZhat F Ω v A hv
  exact card_H1ur ρ _ hρ φ hcl hd

end GlobalTheory.Ord2.UrCard
