import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExtendLin

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Establish `hp : (p : K) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero`. Establish `h1 : ∀ w ∈ D.om, w e = 0`. Introduce `w hw`. Establish `hm : ((p : A) ^ R) • w ∈ D.om'` using `Submodule.mem_sup_right ⟨w, hw, rfl⟩`. Establish `h` using `he _ hm`.

Rewrite `h` using `[LinearMap.smul_apply, Algebra.smul_def, map_pow, map_natCast]`. Conclude with `(mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hp)`. Establish `h2 : Submodule.span K (D.om : Set (Module.Dual K Li)) ≤ LinearMap.ker (Module.Dual.eval K Li e)` using `Submodule.span_le.2 fun w hw => h1 w hw`. Rewrite `h2` using `[D.om_lat.span_eq_top]`. Conclude with `(Module.forall_dual_apply_eq_zero_iff K e).1 fun w => h2 (Submodule.mem_top (x := w))`.
-/
theorem eq_zero_of_forall_om' {A K : Type} [CommRing A] [Field K] [Algebra A K] [CharZero K] {E : Type} [Field E]
    [NumberField E] {c : E ≃+* E} {p R N : ℕ} [Fact p.Prime] {Li : Type} [AddCommGroup Li] [Module K Li]
    (D : HTChart A K c p R N (Module.Dual K Li)) {e : Li} (he : ∀ w ∈ D.om', w e = 0) : e = 0 := by
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h1 : ∀ w ∈ D.om, w e = 0 := by
    intro w hw
    have hm : ((p : A) ^ R) • w ∈ D.om' := Submodule.mem_sup_right ⟨w, hw, rfl⟩
    have h := he _ hm
    rw [LinearMap.smul_apply, Algebra.smul_def, map_pow, map_natCast] at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hp)
  have h2 : Submodule.span K (D.om : Set (Module.Dual K Li)) ≤ LinearMap.ker (Module.Dual.eval K Li e) :=
    Submodule.span_le.2 fun w hw => h1 w hw
  rw [D.om_lat.span_eq_top] at h2
  exact (Module.forall_dual_apply_eq_zero_iff K e).1 fun w => h2 (Submodule.mem_top (x := w))

/- English proof (translation)
Introduce `A K _ _ _ _ _ _ _ E _ _ c hc p R N _ Li _ _ D ρ hact σ d m i hd hex`. Establish `hττ : (σ.comp c.toRingHom).comp c.toRingHom = σ`. Use extensionality with `x`. Simplify using `[hc]`. Establish `hinj` using `IsFractionRing.injective A K`.

Establish `hE : ∀ e ∈ eigSp ρ σ, ∀ w : Module.Dual K Li, eigProj D.ρΩ (σ.comp c.toRingHom) w e = w e` using `fun e he w => eigProj_apply D ρ hc hact (σ.comp c.toRingHom) (by rw [hττ]; exact he) w`. Establish `hvec0 : ∀ g : Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∃ e ∈ eigSp ρ σ, ∀ z : D.omHT (σ.comp c.toRingHom), algebraMap A K d * (z : Module.Dual K Li) e = algebraMap A K (g z)`. Introduce `g`. Take `⟨e, he, hz⟩` from `exists_vec D ρ hc hact (σ.comp c.toRingHom) g`. Rewrite `he` using `[hττ]`.

Use `⟨(algebraMap A K d)⁻¹ • e, Submodule.smul_mem _ _ he, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hz, smul_eq_mul, mul_inv_cancel_left₀ hd]`. Use `choose vec hvecS hvec using hvec0`. Establish `hmem : ∀ w ∈ D.om', ∃ z : D.omHT (σ.comp c.toRingHom), (z : Module.Dual K Li) = eigProj D.ρΩ (σ.comp c.toRingHom) w` using `fun w hw => ⟨⟨_, w, hw, rfl⟩, rfl⟩`. Establish `hsep : ∀ e ∈ eigSp ρ σ, (∀ z : D.omHT (σ.comp c.toRingHom), (z : Module.Dual K Li) e = 0) → e = 0`.

Introduce `e he h`. Use `eq_zero_of_forall_om' D fun w hw => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `hmem w hw`. Rewrite using `[← hE e he w, ← hz]`. Conclude with `h z`.

Establish `hun : ∀ e ∈ eigSp ρ σ, ∀ e' ∈ eigSp ρ σ, (∀ z : D.omHT (σ.comp c.toRingHom), algebraMap A K d * (z : Module.Dual K Li) e = algebraMap A K d * (z : Module.Dual K Li) e') → e = e'`. Introduce `e he e' he' h`. Use `sub_eq_zero.1 (hsep _ (Submodule.sub_mem _ he he') fun z => ?_)` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `mul_left_cancel₀ hd (h z)`.

Use `letI : Module A Li := Module.compHom Li (algebraMap A K)`. Use `haveI : IsScalarTower A K Li := ⟨fun a k v => by`. Express the relevant statement in the definitionally equal form `(a • k) • v = algebraMap A K a • (k • v)`. Rewrite using `[Algebra.smul_def, mul_smul]⟩`. Establish `hsmul : ∀ (a : A) (v : Li), a • v = algebraMap A K a • v` using `fun _ _ => rfl`.

Set `vecL : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] Li` to `{ toFun := vec map_add' := fun g g' => hun _ (hvecS _) _ (Submodule.add_mem _ (hvecS g) (hvecS g')) fun z => by`. Rewrite using `[hvec, map_add, mul_add, hvec, hvec, LinearMap.add_apply, map_add]`. Use the proof step `map_smul' := fun a g => hun _ (hvecS _) _ (by`. Rewrite using `[RingHom.id_apply, hsmul]`. Conclude with `Submodule.smul_mem _ _ (hvecS g)) fun z => by`.

Rewrite using `[hvec, RingHom.id_apply, hsmul, map_smul, smul_eq_mul, mul_left_comm, hvec, LinearMap.smul_apply, smul_eq_mul, map_mul] }`. Establish `hvW : ∀ g, vec g ∈ latOn D (eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range` using `fun g => ⟨hvecS g, fun w hw => by`. Take `⟨z, hz⟩` from `hmem w hw`. Rewrite using `[← hE _ (hvecS g) w, ← hz, hvec]`. Conclude with `⟨_, rfl⟩⟩`.

Set `Wsub : Submodule A Li` to `{ carrier := latOn D (eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun w hw => by`. Rewrite using `[map_add, mul_add]`. Conclude with `add_mem (ha.2 w hw) (hb.2 w hw)⟩`. Use the proof step `zero_mem' := ⟨Submodule.zero_mem _, fun w _ => by`. Rewrite using `[map_zero, mul_zero]`.

Conclude with `zero_mem _⟩`. Use the proof step `smul_mem' := fun a x hx => ⟨by`. Rewrite using `[hsmul]`. Conclude with `Submodule.smul_mem _ _ hx.1, fun w hw => by`. Rewrite using `[hsmul, map_smul, smul_eq_mul, mul_left_comm]`.

Conclude with `mul_mem ⟨a, rfl⟩ (hx.2 w hw)⟩ }`. Establish `hfe : ∀ e ∈ latOn D (eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ f : Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∀ z : D.omHT (σ.comp c.toRingHom), algebraMap A K (f z) = algebraMap A K d * (z : Module.Dual K Li) e`. Introduce `e he`. Establish `h0 : ∀ z : D.omHT (σ.comp c.toRingHom), ∃ a : A, algebraMap A K a = algebraMap A K d * (z : Module.Dual K Li) e`. Introduce `z`.

Take `⟨w, hw, hz⟩` from `z.2`. Establish `hz' : eigProj D.ρΩ (σ.comp c.toRingHom) w = (z : Module.Dual K Li)` using `hz`. Rewrite using `[← hz', hE e he.1 w]`. Conclude with `he.2 w hw`. Use `choose F hF using h0`.

Use `⟨{ toFun := F, map_add' := fun x y => hinj ?_, map_smul' := fun a x => hinj ?_ }, hF⟩` and prove the remaining obligations. Rewrite using `[map_add, hF, hF, hF, Submodule.coe_add, LinearMap.add_apply, mul_add]`. Rewrite using `[RingHom.id_apply, smul_eq_mul, map_mul, hF, hF, Submodule.coe_smul, LinearMap.smul_apply, Algebra.smul_def, mul_left_comm]`. Set `Lv : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] Wsub` to `vecL.codRestrict Wsub hvW`. Establish `hLv : Function.Bijective Lv`.

Prove the components needed by the constructor for the conclusion. Introduce `g g' h`. Establish `h' : vec g = vec g'` using `congrArg Subtype.val h`. Use extensionality with `z`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[← hvec, ← hvec, h']`. Introduce and unpack `⟨e, he⟩`. Take `⟨f, hf⟩` from `hfe e he`. Use `⟨f, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `vec f = e`.

Conclude with `hun _ (hvecS f) _ he.1 fun z => by rw [hvec, hf]`. Set `Leq` to `LinearEquiv.ofBijective Lv hLv`. Establish `hLeq : ∀ (e : Li) (he : e ∈ Wsub), vec (Leq.symm ⟨e, he⟩) = e` using `fun e he => congrArg Subtype.val (Leq.apply_symm_apply ⟨e, he⟩)`. Take `⟨G, hG⟩` from `exists_extend_lin (K := K) Wsub (((Algebra.linearMap A K).compLeft (Fin N)) ∘ₗ i ∘ₗ Leq.symm.toLinearMap)`. Take `⟨⟨r, hr⟩, -⟩` from `hex`.

Set `Rr : (Fin N → K) →ₗ[K] Li` to `Fintype.linearCombination K fun k => vec (r (Pi.single k 1))`. Establish `hRr : ∀ y : Fin N → A, Rr (fun l => algebraMap A K (y l)) = vec (r y)`. Introduce `y`. Establish `hy : y = ∑ k, y k • Pi.single k (1 : A)`. Use extensionality with `l`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `h1 : vec (r y) = vecL (r y)` using `rfl`. Rewrite using `[h1]`. Use `conv_rhs => rw [hy]`. Rewrite using `[map_sum, map_sum]`.

Simplify using `only [Rr, Fintype.linearCombination_apply, map_smul, hsmul]`. Both sides reduce to the same expression. Use `⟨G, Rr, fun e he => ?_, fun k => ?_, fun e he => ?_⟩` and prove the remaining obligations. Use `⟨Leq.symm ⟨e, he⟩, fun z => ?_, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[← hvec, hLeq e he]`.

Use `hG ⟨e, he⟩` as an intermediate fact. Conclude with `congrFun this l`. Establish `h1 : Rr (Pi.single k 1) = vec (r (Pi.single k 1))`. Simplify using `[Rr, Fintype.linearCombination_apply_single]`. Rewrite using `[h1]`.

Conclude with `hvW _`. Take `⟨w', hw'⟩` from `hr (Leq.symm ⟨e, he⟩)`. Use `⟨vec w', hvW w', ?_⟩` and prove the remaining obligations. Establish `h1 : G e = fun l => algebraMap A K (i (Leq.symm ⟨e, he⟩) l)` using `hG ⟨e, he⟩`. Establish `h2 : vec (r (i (Leq.symm ⟨e, he⟩))) = vecL (Leq.symm ⟨e, he⟩) + (((p : A) ^ m) • vecL w')`.

Express the relevant statement in the definitionally equal form `vecL _ = _`. Rewrite using `[hw', map_add, map_smul]`. Rewrite using `[h1, hRr, h2]`. Express the relevant statement in the definitionally equal form `vec (Leq.symm ⟨e, he⟩) + _ = _`. Rewrite using `[hLeq e he, hsmul, map_pow, map_natCast]`.

Both sides reduce to the same expression.
-/
theorem exists_lift_retract : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Li : Type) [AddCommGroup Li] [Module K Li] (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li), (∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* K) (d : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), algebraMap A K d ≠ 0 → D.ExactMod σ m i → ∃ (J : Li →ₗ[K] (Fin N → K)) (Rr : (Fin N → K) →ₗ[K] Li), (∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ f : Module.Dual A (D.omHT (σ.comp c.toRingHom)), (∀ z : D.omHT (σ.comp c.toRingHom), algebraMap A K (f z) = algebraMap A K d * (z : Module.Dual K Li) e) ∧ ∀ l, J e l = algebraMap A K (i f l)) ∧ (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range) ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, Rr (J e) = e + ((p : K) ^ m) • e' := by
  intro A K _ _ _ _ _ _ _ E _ _ c hc p R N _ Li _ _ D ρ hact σ d m i hd hex
  classical
  have hττ : (σ.comp c.toRingHom).comp c.toRingHom = σ := by
    ext x
    simp [hc]
  have hinj := IsFractionRing.injective A K
  have hE : ∀ e ∈ eigSp ρ σ, ∀ w : Module.Dual K Li, eigProj D.ρΩ (σ.comp c.toRingHom) w e = w e :=
    fun e he w => eigProj_apply D ρ hc hact (σ.comp c.toRingHom) (by rw [hττ]; exact he) w
  have hvec0 : ∀ g : Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∃ e ∈ eigSp ρ σ,
      ∀ z : D.omHT (σ.comp c.toRingHom),
        algebraMap A K d * (z : Module.Dual K Li) e = algebraMap A K (g z) := by
    intro g
    obtain ⟨e, he, hz⟩ := exists_vec D ρ hc hact (σ.comp c.toRingHom) g
    rw [hττ] at he
    refine ⟨(algebraMap A K d)⁻¹ • e, Submodule.smul_mem _ _ he, fun z => ?_⟩
    rw [map_smul, hz, smul_eq_mul, mul_inv_cancel_left₀ hd]
  choose vec hvecS hvec using hvec0
  have hmem : ∀ w ∈ D.om', ∃ z : D.omHT (σ.comp c.toRingHom),
      (z : Module.Dual K Li) = eigProj D.ρΩ (σ.comp c.toRingHom) w :=
    fun w hw => ⟨⟨_, w, hw, rfl⟩, rfl⟩
  have hsep : ∀ e ∈ eigSp ρ σ, (∀ z : D.omHT (σ.comp c.toRingHom), (z : Module.Dual K Li) e = 0) → e = 0 := by
    intro e he h
    refine eq_zero_of_forall_om' D fun w hw => ?_
    obtain ⟨z, hz⟩ := hmem w hw
    rw [← hE e he w, ← hz]
    exact h z
  have hun : ∀ e ∈ eigSp ρ σ, ∀ e' ∈ eigSp ρ σ, (∀ z : D.omHT (σ.comp c.toRingHom),
      algebraMap A K d * (z : Module.Dual K Li) e = algebraMap A K d * (z : Module.Dual K Li) e') → e = e' := by
    intro e he e' he' h
    refine sub_eq_zero.1 (hsep _ (Submodule.sub_mem _ he he') fun z => ?_)
    rw [map_sub, sub_eq_zero]
    exact mul_left_cancel₀ hd (h z)
  letI : Module A Li := Module.compHom Li (algebraMap A K)
  haveI : IsScalarTower A K Li := ⟨fun a k v => by
    change (a • k) • v = algebraMap A K a • (k • v)
    rw [Algebra.smul_def, mul_smul]⟩
  have hsmul : ∀ (a : A) (v : Li), a • v = algebraMap A K a • v := fun _ _ => rfl
  let vecL : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] Li :=
    { toFun := vec
      map_add' := fun g g' => hun _ (hvecS _) _ (Submodule.add_mem _ (hvecS g) (hvecS g')) fun z => by
        rw [hvec, map_add, mul_add, hvec, hvec, LinearMap.add_apply, map_add]
      map_smul' := fun a g => hun _ (hvecS _) _ (by
          rw [RingHom.id_apply, hsmul]
          exact Submodule.smul_mem _ _ (hvecS g)) fun z => by
        rw [hvec, RingHom.id_apply, hsmul, map_smul, smul_eq_mul, mul_left_comm, hvec, LinearMap.smul_apply,
          smul_eq_mul, map_mul] }
  have hvW : ∀ g, vec g ∈ latOn D (eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range := fun g =>
    ⟨hvecS g, fun w hw => by
      obtain ⟨z, hz⟩ := hmem w hw
      rw [← hE _ (hvecS g) w, ← hz, hvec]
      exact ⟨_, rfl⟩⟩
  let Wsub : Submodule A Li :=
    { carrier := latOn D (eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range
      add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun w hw => by
        rw [map_add, mul_add]
        exact add_mem (ha.2 w hw) (hb.2 w hw)⟩
      zero_mem' := ⟨Submodule.zero_mem _, fun w _ => by
        rw [map_zero, mul_zero]
        exact zero_mem _⟩
      smul_mem' := fun a x hx => ⟨by
          rw [hsmul]
          exact Submodule.smul_mem _ _ hx.1, fun w hw => by
        rw [hsmul, map_smul, smul_eq_mul, mul_left_comm]
        exact mul_mem ⟨a, rfl⟩ (hx.2 w hw)⟩ }
  have hfe : ∀ e ∈ latOn D (eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range,
      ∃ f : Module.Dual A (D.omHT (σ.comp c.toRingHom)),
        ∀ z : D.omHT (σ.comp c.toRingHom),
          algebraMap A K (f z) = algebraMap A K d * (z : Module.Dual K Li) e := by
    intro e he
    have h0 : ∀ z : D.omHT (σ.comp c.toRingHom), ∃ a : A,
        algebraMap A K a = algebraMap A K d * (z : Module.Dual K Li) e := by
      intro z
      obtain ⟨w, hw, hz⟩ := z.2
      have hz' : eigProj D.ρΩ (σ.comp c.toRingHom) w = (z : Module.Dual K Li) := hz
      rw [← hz', hE e he.1 w]
      exact he.2 w hw
    choose F hF using h0
    refine ⟨{ toFun := F, map_add' := fun x y => hinj ?_, map_smul' := fun a x => hinj ?_ }, hF⟩
    · rw [map_add, hF, hF, hF, Submodule.coe_add, LinearMap.add_apply, mul_add]
    · rw [RingHom.id_apply, smul_eq_mul, map_mul, hF, hF, Submodule.coe_smul, LinearMap.smul_apply,
        Algebra.smul_def, mul_left_comm]
  let Lv : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] Wsub := vecL.codRestrict Wsub hvW
  have hLv : Function.Bijective Lv := by
    constructor
    · intro g g' h
      have h' : vec g = vec g' := congrArg Subtype.val h
      ext z
      apply hinj
      rw [← hvec, ← hvec, h']
    · rintro ⟨e, he⟩
      obtain ⟨f, hf⟩ := hfe e he
      refine ⟨f, Subtype.ext ?_⟩
      change vec f = e
      exact hun _ (hvecS f) _ he.1 fun z => by rw [hvec, hf]
  let Leq := LinearEquiv.ofBijective Lv hLv
  have hLeq : ∀ (e : Li) (he : e ∈ Wsub), vec (Leq.symm ⟨e, he⟩) = e := fun e he =>
    congrArg Subtype.val (Leq.apply_symm_apply ⟨e, he⟩)
  obtain ⟨G, hG⟩ := exists_extend_lin (K := K) Wsub
    (((Algebra.linearMap A K).compLeft (Fin N)) ∘ₗ i ∘ₗ Leq.symm.toLinearMap)
  obtain ⟨⟨r, hr⟩, -⟩ := hex
  let Rr : (Fin N → K) →ₗ[K] Li := Fintype.linearCombination K fun k => vec (r (Pi.single k 1))
  have hRr : ∀ y : Fin N → A, Rr (fun l => algebraMap A K (y l)) = vec (r y) := by
    intro y
    have hy : y = ∑ k, y k • Pi.single k (1 : A) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    have h1 : vec (r y) = vecL (r y) := rfl
    rw [h1]
    conv_rhs => rw [hy]
    rw [map_sum, map_sum]
    simp only [Rr, Fintype.linearCombination_apply, map_smul, hsmul]
    rfl
  refine ⟨G, Rr, fun e he => ?_, fun k => ?_, fun e he => ?_⟩
  · refine ⟨Leq.symm ⟨e, he⟩, fun z => ?_, fun l => ?_⟩
    · rw [← hvec, hLeq e he]
    · have := hG ⟨e, he⟩
      exact congrFun this l
  · have h1 : Rr (Pi.single k 1) = vec (r (Pi.single k 1)) := by
      simp [Rr, Fintype.linearCombination_apply_single]
    rw [h1]
    exact hvW _
  · obtain ⟨w', hw'⟩ := hr (Leq.symm ⟨e, he⟩)
    refine ⟨vec w', hvW w', ?_⟩
    have h1 : G e = fun l => algebraMap A K (i (Leq.symm ⟨e, he⟩) l) := hG ⟨e, he⟩
    have h2 : vec (r (i (Leq.symm ⟨e, he⟩))) = vecL (Leq.symm ⟨e, he⟩) + (((p : A) ^ m) • vecL w') := by
      change vecL _ = _
      rw [hw', map_add, map_smul]
    rw [h1, hRr, h2]
    change vec (Leq.symm ⟨e, he⟩) + _ = _
    rw [hLeq e he, hsmul, map_pow, map_natCast]
    rfl

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
