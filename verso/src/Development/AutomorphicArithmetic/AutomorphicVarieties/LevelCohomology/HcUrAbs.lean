import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

namespace UpperTheory.V.X.UnramifiedH1RankEqH0

variable {k D M : Type} [Field k] [Group D] [AddCommGroup M] [Module k M]

private def NI (ρ : Representation k D M) (I : Subgroup D) : Submodule k M where
  carrier := {m | ∀ s ∈ I, ρ s m = m}
  zero_mem' := fun s _ => map_zero _
  add_mem' := fun {a b} ha hb s hs => by rw [map_add, ha s hs, hb s hs]
  smul_mem' c a ha s hs := by rw [map_smul, ha s hs]

/- English proof (translation)
Introduce `s hs`. Establish `h1` using `hm (g⁻¹ * s * g) (by simpa using hI.conj_mem s hs g⁻¹)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]`. Use `congr 2`.

Use `group`. Use `_ = ρ g m := by rw [h1]`.
-/
private theorem NI_stable (ρ : Representation k D M) (I : Subgroup D) [hI : I.Normal] (g : D) {m : M}
    (hm : m ∈ NI ρ I) : ρ g m ∈ NI ρ I := by
  intro s hs
  have h1 := hm (g⁻¹ * s * g) (by simpa using hI.conj_mem s hs g⁻¹)
  calc ρ s (ρ g m) = ρ g (ρ (g⁻¹ * s * g) m) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group
    _ = ρ g m := by rw [h1]

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.
-/
private theorem inv_apply (ρ : Representation k D M) (g : D) (m : M) : ρ g⁻¹ (ρ g m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.
-/
private theorem apply_inv (ρ : Representation k D M) (g : D) (m : M) : ρ g (ρ g⁻¹ m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable [TopologicalSpace D] [IsTopologicalGroup D]

/- English proof (translation)
Use `Subgroup.topologicalClosure_minimal (I ⊔ Subgroup.zpowers σ) (sup_le hI ((Subgroup.zpowers_le).2 hσ)) hH` as an intermediate fact. Rewrite `this` using `[hd]`. Conclude with `this (Subgroup.mem_top g)`.
-/
private theorem all_of_closed {I : Subgroup D} {σ : D}
    (hd : (I ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤) (H : Subgroup D) (hH : IsClosed (H : Set D))
    (hI : I ≤ H) (hσ : σ ∈ H) (g : D) : g ∈ H := by
  have := Subgroup.topologicalClosure_minimal (I ⊔ Subgroup.zpowers σ)
    (sup_le hI ((Subgroup.zpowers_le).2 hσ)) hH
  rw [hd] at this
  exact this (Subgroup.mem_top g)

/- English proof (translation)
Establish `hn : 0 < orderOf e` using `orderOf_pos e`. Use `haveI : NeZero (orderOf e) := ⟨hn.ne'⟩`. Take `⟨d, hdl, hdI, hdφ⟩` from `hd (orderOf e) hn`. Set `f : Multiplicative (ZMod (orderOf e)) →* E` to `MonoidHom.mk' (fun x => e ^ (Multiplicative.toAdd x).val) (by`. Introduce `a b`.

Simplify using `only [toAdd_mul, ZMod.val_add, pow_mod_orderOf, pow_add])`. Establish `hf1 : f (Multiplicative.ofAdd 1) = e` using `by show e ^ (1 : ZMod (orderOf e)).val = e`. Rewrite using `[ZMod.val_one_eq_one_mod, pow_mod_orderOf, pow_one]`. Use `⟨f.comp d, hdl.comp f, fun s hs => by simp [hdI s hs], ?_⟩` and prove the remaining obligations. Use `show f (d φ) = e`.

Rewrite using `[hdφ, hf1]`.
-/
private theorem exists_hom {E : Type} [Group E] [Finite E] {I : Subgroup D} {φ : D}
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) (e : E) :
    ∃ w : D →* E, IsLocallyConstant w ∧ (∀ s ∈ I, w s = 1) ∧ w φ = e := by
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
  refine ⟨f.comp d, hdl.comp f, fun s hs => by simp [hdI s hs], ?_⟩
  show f (d φ) = e
  rw [hdφ, hf1]

variable [TopologicalSpace M] [DiscreteTopology M]

/- English proof (translation)
Set `e : Equiv.Perm (NI ρ I)` to `{ toFun := fun m => ⟨x + ρ φ m, add_mem hx (NI_stable ρ I φ m.2)⟩ invFun := fun m => ⟨ρ φ⁻¹ (m - x), NI_stable ρ I _ (sub_mem m.2 hx)⟩ left_inv := fun m => Subtype.ext (by simp only [add_sub_cancel_left, inv_apply]) right_inv := fun m => Subtype.ext (by simp only [apply_inv, add_ …`. Take `⟨w, hw, hwI, hwφ⟩` from `exists_hom hd e`. Establish `hc : ∀ m : NI ρ I, Continuous fun g => ((w g m : NI ρ I) : M)` using `fun m => (hw.comp fun σ : Equiv.Perm (NI ρ I) => ((σ m : NI ρ I) : M)).continuous`. Set `H : Subgroup D` to `{ carrier := {g | ∀ m m' : NI ρ I, ((w g m : NI ρ I) : M) - (w g m' : NI ρ I) = ρ g ((m : M) - m')} mul_mem' := fun {a b} ha hb m m' => by`. Rewrite using `[map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ha, hb, Module.End.mul_apply]`.

Use the proof step `one_mem' := fun m m' => by simp`. Use the proof step `inv_mem' := fun {a} ha m m' => by`. Establish `h1` using `ha (w a⁻¹ m) (w a⁻¹ m')`. Rewrite `h1` using `[← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply, Equiv.Perm.one_apply]`. Rewrite using `[h1, inv_apply] }`.

Establish `hH : ∀ g, g ∈ H`. Use `all_of_closed hcl H ?_ (fun s hs m m' => ?_) (fun m m' => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsClosed {g | ∀ m m' : NI ρ I, ((w g m : NI ρ I) : M) - (w g m' : NI ρ I) = ρ g ((m : M) - m')}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isClosed_iInter fun m => isClosed_iInter fun m' => isClosed_eq ((hc m).sub (hc m')) (Continuous.comp (f := fun g : D => (g, (m : M) - m')) hρ (by fun_prop))`.

Rewrite using `[hwI s hs, (sub_mem m.2 m'.2 : _ ∈ NI ρ I) s hs]`. Both sides reduce to the same expression. Rewrite using `[hwφ, map_sub]`. Express the relevant statement in the definitionally equal form `x + ρ φ m - (x + ρ φ m') = _`. Normalize the expressions using the abelian group laws.

Use `⟨fun g => ((w g 0 : NI ρ I) : M), ⟨hc 0, fun g h => ?_⟩, fun s hs => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hH g (w h 0) 0`. Rewrite `h1` using `[Submodule.coe_zero, sub_zero]`. Simplify using `only [map_mul, Equiv.Perm.mul_apply]`. Rewrite using `[← h1]`.

Normalize the expressions using the abelian group laws. Simplify using `only [hwI s hs]`. Both sides reduce to the same expression. Simplify using `only [hwφ]`. Express the relevant statement in the definitionally equal form `x + ρ φ 0 = x`.

Simplify using the standard rewrite rules.
-/
private theorem exists_cocycle [Finite M] (ρ : Representation k D M) (hρ : ContAction ρ) {I : Subgroup D} [I.Normal] {φ : D}
    (hcl : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) {x : M} (hx : x ∈ NI ρ I) :
    ∃ z ∈ Z1 ρ, (∀ s ∈ I, z s = 0) ∧ z φ = x := by
  let e : Equiv.Perm (NI ρ I) :=
    { toFun := fun m => ⟨x + ρ φ m, add_mem hx (NI_stable ρ I φ m.2)⟩
      invFun := fun m => ⟨ρ φ⁻¹ (m - x), NI_stable ρ I _ (sub_mem m.2 hx)⟩
      left_inv := fun m => Subtype.ext (by simp only [add_sub_cancel_left, inv_apply])
      right_inv := fun m => Subtype.ext (by simp only [apply_inv, add_sub_cancel]) }
  obtain ⟨w, hw, hwI, hwφ⟩ := exists_hom hd e
  have hc : ∀ m : NI ρ I, Continuous fun g => ((w g m : NI ρ I) : M) := fun m =>
    (hw.comp fun σ : Equiv.Perm (NI ρ I) => ((σ m : NI ρ I) : M)).continuous
  let H : Subgroup D :=
    { carrier := {g | ∀ m m' : NI ρ I, ((w g m : NI ρ I) : M) - (w g m' : NI ρ I) = ρ g ((m : M) - m')}
      mul_mem' := fun {a b} ha hb m m' => by
        rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ha, hb, Module.End.mul_apply]
      one_mem' := fun m m' => by simp
      inv_mem' := fun {a} ha m m' => by
        have h1 := ha (w a⁻¹ m) (w a⁻¹ m')
        rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Equiv.Perm.one_apply, Equiv.Perm.one_apply] at h1
        rw [h1, inv_apply] }
  have hH : ∀ g, g ∈ H := by
    refine all_of_closed hcl H ?_ (fun s hs m m' => ?_) (fun m m' => ?_)
    · change IsClosed {g | ∀ m m' : NI ρ I, ((w g m : NI ρ I) : M) - (w g m' : NI ρ I) = ρ g ((m : M) - m')}
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun m => isClosed_iInter fun m' => isClosed_eq ((hc m).sub (hc m'))
        (Continuous.comp (f := fun g : D => (g, (m : M) - m')) hρ (by fun_prop))
    · rw [hwI s hs, (sub_mem m.2 m'.2 : _ ∈ NI ρ I) s hs]
      rfl
    · rw [hwφ, map_sub]
      change x + ρ φ m - (x + ρ φ m') = _
      abel
  refine ⟨fun g => ((w g 0 : NI ρ I) : M), ⟨hc 0, fun g h => ?_⟩, fun s hs => ?_, ?_⟩
  · have h1 := hH g (w h 0) 0
    rw [Submodule.coe_zero, sub_zero] at h1
    simp only [map_mul, Equiv.Perm.mul_apply]
    rw [← h1]
    abel
  · simp only [hwI s hs]
    rfl
  · simp only [hwφ]
    change x + ρ φ 0 = x
    simp

/- English proof (translation)
Establish `d1 : d 1 = 0`. Use `hd0.2 1 1` as an intermediate fact. Simplify using `using this`. Set `H : Subgroup D` to `{ carrier := {g | d g = 0} mul_mem' := fun {a b} ha hb => by`. Express the relevant statement in the definitionally equal form `d (a * b) = 0`.

Rewrite using `[hd0.2, show d a = 0 from ha, show d b = 0 from hb]`. Simplify using the standard rewrite rules. Use the proof step `one_mem' := d1`. Use the proof step `inv_mem' := fun {a} ha => by`. Use `hd0.2 a⁻¹ a` as an intermediate fact.

Rewrite `this` using `[inv_mul_cancel, d1, show d a = 0 from ha]`. Express the relevant statement in the definitionally equal form `d a⁻¹ = 0`. Simplify using `using this.symm }`. Conclude with `all_of_closed hcl H (isClosed_eq hd0.1 continuous_const) hI hφ g`.
-/
private theorem eq_zero_of (ρ : Representation k D M) {I : Subgroup D} {φ : D}
    (hcl : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) {d : D → M} (hd0 : d ∈ Z1 ρ)
    (hI : ∀ s ∈ I, d s = 0) (hφ : d φ = 0) (g : D) : d g = 0 := by
  have d1 : d 1 = 0 := by
    have := hd0.2 1 1
    simpa using this
  let H : Subgroup D :=
    { carrier := {g | d g = 0}
      mul_mem' := fun {a b} ha hb => by
        change d (a * b) = 0
        rw [hd0.2, show d a = 0 from ha, show d b = 0 from hb]
        simp
      one_mem' := d1
      inv_mem' := fun {a} ha => by
        have := hd0.2 a⁻¹ a
        rw [inv_mul_cancel, d1, show d a = 0 from ha] at this
        change d a⁻¹ = 0
        simpa using this.symm }
  exact all_of_closed hcl H (isClosed_eq hd0.1 continuous_const) hI hφ g

private def Z0 (ρ : Representation k D M) (I : Subgroup D) : Submodule k (Z1 ρ) where
  carrier := {z | ∀ s ∈ I, z.1 s = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb s hs => by
    change a.1 s + b.1 s = 0
    rw [ha s hs, hb s hs, add_zero]
  smul_mem' c a ha s hs := by
    change c • a.1 s = 0
    rw [ha s hs, smul_zero]

/- English proof (translation)
Introduce `s hs`. Establish `h1` using `z.1.2.2 s g`. Establish `h2` using `z.1.2.2 g (g⁻¹ * s * g)`. Rewrite `h1` using `[z.2 s hs, zero_add]`. Rewrite `h2` using `[z.2 (g⁻¹ * s * g) (by simpa using hI.conj_mem s hs g⁻¹), map_zero, add_zero, show g * (g⁻¹ * s * g) = s * g by group]`.

Rewrite using `[← h1, h2]`.
-/
private theorem val_mem (ρ : Representation k D M) (I : Subgroup D) [hI : I.Normal] (z : Z0 ρ I) (g : D) :
    z.1.1 g ∈ NI ρ I := by
  intro s hs
  have h1 := z.1.2.2 s g
  have h2 := z.1.2.2 g (g⁻¹ * s * g)
  rw [z.2 s hs, zero_add] at h1
  rw [z.2 (g⁻¹ * s * g) (by simpa using hI.conj_mem s hs g⁻¹), map_zero, add_zero,
    show g * (g⁻¹ * s * g) = s * g by group] at h2
  rw [← h1, h2]

end UpperTheory.V.X.UnramifiedH1RankEqH0

open UpperTheory.V.X.UnramifiedH1RankEqH0 in
/- English proof (translation)
Introduce `k D M _ _ _ _ _ _ _ _ _ ρ hρ I _ φ hcl hd`. Use `haveI : FiniteDimensional k M := Module.Finite.of_finite`. Set `ev : Z0 ρ I →ₗ[k] NI ρ I` to `{ toFun := fun z => ⟨z.1.1 φ, val_mem ρ I z φ⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hev : Function.Bijective ev`. Use `⟨(injective_iff_map_eq_zero ev).2 fun z hz => ?_, fun x => ?_⟩` and prove the remaining obligations.

Conclude with `Subtype.ext (Subtype.ext (funext (eq_zero_of ρ hcl z.1.2 z.2 (congrArg Subtype.val hz))))`. Take `⟨z, hz, hzI, hzφ⟩` from `exists_cocycle ρ hρ hcl hd x.2`. Conclude with `⟨⟨⟨z, hz⟩, hzI⟩, Subtype.ext hzφ⟩`. Set `E` to `LinearEquiv.ofBijective ev hev`. Use `haveI : FiniteDimensional k (Z0 ρ I) := E.symm.finiteDimensional`.

Set `p : Z0 ρ I →ₗ[k] H1 ρ` to `(Submodule.mkQ _).comp (Z0 ρ I).subtype`. Set `δ : NI ρ I →ₗ[k] Z0 ρ I` to `{ toFun := fun m => ⟨⟨d0 ρ m, coboundaries_le_cocycles ρ hρ ⟨m, rfl⟩⟩, fun s hs => sub_eq_zero.2 (m.2 s hs)⟩ map_add' := fun a b => Subtype.ext (Subtype.ext (map_add (d0 ρ) _ _)) map_smul' := fun c a => Subtype.ext (Subtype.ext (map_smul (d0 ρ) _ _)) }`. Establish `h1 : LinearMap.range p = H1ur ρ I`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨z, rfl⟩`.

Use `(Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun s => ?_⟩)` and prove the remaining obligations. Rewrite using `[map_zero, sub_zero]`. Conclude with `z.2 s s.2`. Introduce `c hc`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ c`.

Take `⟨m, hm⟩` from `(mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hc)`. Use `⟨⟨z - ⟨d0 ρ m, coboundaries_le_cocycles ρ hρ ⟨m, rfl⟩⟩, fun s hs => sub_eq_zero.2 (show z.1 s = d0 ρ m s from hm ⟨s, hs⟩)⟩, ?_⟩` and prove the remaining obligations. Use `(Submodule.Quotient.eq _).2 ?_` and prove the remaining obligations. Rewrite using `[Submodule.subtype_apply, sub_sub_cancel_left]`. Conclude with `neg_mem ⟨m, rfl⟩`.

Establish `h2 : LinearMap.range δ = LinearMap.ker p`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨m, rfl⟩`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 ⟨m, rfl⟩`. Introduce `z hz`.

Take `⟨m, hm⟩` from `(mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hz)`. Use `⟨⟨m, fun s hs => sub_eq_zero.1 ((hm s).symm.trans (z.2 s hs))⟩, ?_⟩` and prove the remaining obligations. Conclude with `Subtype.ext (Subtype.ext (funext fun g => (hm g).symm))`. Establish `h3 : (LinearMap.ker δ).map (NI ρ I).subtype = H0 ρ`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce and unpack `_ ⟨m, hm, rfl⟩ g`. Conclude with `sub_eq_zero.1 (congrFun (congrArg (fun z : Z0 ρ I => z.1.1) hm) g)`. Introduce `m hm`. Conclude with `⟨⟨m, fun s _ => hm s⟩, Subtype.ext (Subtype.ext (funext fun g => sub_eq_zero.2 (hm g))), rfl⟩`. Establish `a1` using `p.finrank_range_add_finrank_ker`.

Establish `a2` using `δ.finrank_range_add_finrank_ker`. Establish `a3` using `E.finrank_eq`. Rewrite using `[← h1, ← h3, Submodule.finrank_map_subtype_eq]`. Rewrite `a2` using `[h2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.X.urAbs :
    ∀ {k D M : Type} [Field k] [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M), ContAction ρ → ∀ (I : Subgroup D) [I.Normal] (φ : D), (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ → (∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) → finrank k (H1ur ρ I) = finrank k (H0 ρ) := by
  intro k D M _ _ _ _ _ _ _ _ _ ρ hρ I _ φ hcl hd
  haveI : FiniteDimensional k M := Module.Finite.of_finite
  let ev : Z0 ρ I →ₗ[k] NI ρ I :=
    { toFun := fun z => ⟨z.1.1 φ, val_mem ρ I z φ⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Bijective ev := by
    refine ⟨(injective_iff_map_eq_zero ev).2 fun z hz => ?_, fun x => ?_⟩
    · exact Subtype.ext (Subtype.ext (funext
        (eq_zero_of ρ hcl z.1.2 z.2 (congrArg Subtype.val hz))))
    · obtain ⟨z, hz, hzI, hzφ⟩ := exists_cocycle ρ hρ hcl hd x.2
      exact ⟨⟨⟨z, hz⟩, hzI⟩, Subtype.ext hzφ⟩
  let E := LinearEquiv.ofBijective ev hev
  haveI : FiniteDimensional k (Z0 ρ I) := E.symm.finiteDimensional
  let p : Z0 ρ I →ₗ[k] H1 ρ := (Submodule.mkQ _).comp (Z0 ρ I).subtype
  let δ : NI ρ I →ₗ[k] Z0 ρ I :=
    { toFun := fun m => ⟨⟨d0 ρ m, coboundaries_le_cocycles ρ hρ ⟨m, rfl⟩⟩, fun s hs => sub_eq_zero.2 (m.2 s hs)⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (map_add (d0 ρ) _ _))
      map_smul' := fun c a => Subtype.ext (Subtype.ext (map_smul (d0 ρ) _ _)) }
  have h1 : LinearMap.range p = H1ur ρ I := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun s => ?_⟩)
      rw [map_zero, sub_zero]
      exact z.2 s s.2
    · intro c hc
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hc)
      refine ⟨⟨z - ⟨d0 ρ m, coboundaries_le_cocycles ρ hρ ⟨m, rfl⟩⟩, fun s hs =>
        sub_eq_zero.2 (show z.1 s = d0 ρ m s from hm ⟨s, hs⟩)⟩, ?_⟩
      refine (Submodule.Quotient.eq _).2 ?_
      rw [Submodule.subtype_apply, sub_sub_cancel_left]
      exact neg_mem ⟨m, rfl⟩
  have h2 : LinearMap.range δ = LinearMap.ker p := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨m, rfl⟩
    · intro z hz
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hz)
      refine ⟨⟨m, fun s hs => sub_eq_zero.1 ((hm s).symm.trans (z.2 s hs))⟩, ?_⟩
      exact Subtype.ext (Subtype.ext (funext fun g => (hm g).symm))
  have h3 : (LinearMap.ker δ).map (NI ρ I).subtype = H0 ρ := by
    apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩ g
      exact sub_eq_zero.1 (congrFun (congrArg (fun z : Z0 ρ I => z.1.1) hm) g)
    · intro m hm
      exact ⟨⟨m, fun s _ => hm s⟩, Subtype.ext (Subtype.ext (funext fun g => sub_eq_zero.2 (hm g))), rfl⟩
  have a1 := p.finrank_range_add_finrank_ker
  have a2 := δ.finrank_range_add_finrank_ker
  have a3 := E.finrank_eq
  rw [← h1, ← h3, Submodule.finrank_map_subtype_eq]
  rw [h2] at a2
  omega
