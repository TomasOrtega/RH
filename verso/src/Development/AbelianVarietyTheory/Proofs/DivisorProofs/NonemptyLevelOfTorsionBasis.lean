import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RealMult

/- English proof (translation)
Establish `hzero : ∀ x, act 0 x = 1` using `fun x ↦ by`. Use `hadd 0 0 x` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_mul.1 this`. Establish `hnat : ∀ (n : ℕ) x, act (n : O) x = x ^ n` using `fun n x ↦ by`.

Proceed by induction on `n with`. Consider the case `zero => simp [hzero]`. Consider the case `succ n ih => rw [Nat.cast_succ, hadd, ih, hone, pow_succ]`. Set `f : (Fin 2 → G) → (O × O →+ Additive G)` to `fun r ↦ AddMonoidHom.mk' (fun c ↦ Additive.ofMul (act c.1 (r 0) * act c.2 (r 1))) (fun c d ↦ by`. Rewrite using `[← ofMul_mul, Prod.fst_add, Prod.snd_add, hadd, hadd, _root_.mul_mul_mul_comm])`.

Set `I : AddSubgroup O` to `(Ideal.span {(N : O)}).toAddSubgroup`. Establish `hker : ∀ r : Fin 2 → G, (∀ i, r i ^ N = 1) → (∀ a b, act a (r 0) * act b (r 1) = 1 → (N : O) ∣ a ∧ (N : O) ∣ b) → (f r).ker = I.prod I`. Introduce `r hr ir`. Use extensionality with `⟨a, b⟩`. Rewrite using `[AddMonoidHom.mem_ker, AddSubgroup.mem_prod]`.

Express the relevant statement in the definitionally equal form `act a (r 0) * act b (r 1) = 1 ↔ a ∈ Ideal.span {(N : O)} ∧ b ∈ Ideal.span {(N : O)}`. Rewrite using `[Ideal.mem_span_singleton, Ideal.mem_span_singleton]`. Use `⟨ir a b, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩`. Rewrite using `[hmul, hmul, hnat, hnat, hr, hr, map_one, map_one, _root_.one_mul]`.

Establish `hI : I.index ≠ 0`. Establish `: Finite (O ⧸ I)` using `‹Finite (O ⧸ Ideal.span {(N : O)})›`. Conclude with `AddSubgroup.index_ne_zero_of_finite`. Establish `cp : Nat.card (f p).range = I.index * I.index`. Rewrite using `[← AddSubgroup.index_ker, hker p hp ip, AddSubgroup.index_prod]`.

Establish `cq : Nat.card (f q).range = I.index * I.index`. Rewrite using `[← AddSubgroup.index_ker, hker q hq iq, AddSubgroup.index_prod]`. Establish `: Finite (f q).range` using `Nat.finite_of_card_ne_zero (cq ▸ mul_ne_zero hI hI)`. Establish `hle : (f p).range ≤ (f q).range`. Introduce and unpack `_ ⟨⟨a, b⟩, rfl⟩`.

Take `⟨c, d, h⟩` from `sq (act a (p 0) * act b (p 1)) (by`. Rewrite using `[mul_pow, ← map_pow, ← map_pow, hp, hp, map_one, map_one, _root_.one_mul])`. Conclude with `⟨(c, d), congrArg Additive.ofMul h.symm⟩`. Establish `heq` using `AddSubgroup.eq_of_le_of_card_ge hle (by rw [cp, cq])`. Introduce `y hy`.

Take `⟨c, d, h⟩` from `sq y hy`. Establish `hm : Additive.ofMul y ∈ (f p).range` using `heq ▸ ⟨(c, d), congrArg Additive.ofMul h.symm⟩`. Take `⟨⟨a, b⟩, hab⟩` from `hm`. Conclude with `⟨a, b, (congrArg Additive.toMul hab).symm⟩`.
-/
theorem span_torsion_of_indep {O : Type} [CommRing O] {G : Type} [CommGroup G] (N : ℕ)
    [Finite (O ⧸ Ideal.span {(N : O)})] (act : O → G →* G) (hone : ∀ x, act 1 x = x)
    (hmul : ∀ a b x, act (a * b) x = act b (act a x)) (hadd : ∀ a b x, act (a + b) x = act a x * act b x)
    (p q : Fin 2 → G) (hp : ∀ i, p i ^ N = 1) (hq : ∀ i, q i ^ N = 1)
    (ip : ∀ a b, act a (p 0) * act b (p 1) = 1 → (N : O) ∣ a ∧ (N : O) ∣ b)
    (iq : ∀ a b, act a (q 0) * act b (q 1) = 1 → (N : O) ∣ a ∧ (N : O) ∣ b)
    (sq : ∀ y, y ^ N = 1 → ∃ a b, y = act a (q 0) * act b (q 1)) :
    ∀ y, y ^ N = 1 → ∃ a b, y = act a (p 0) * act b (p 1) := by
  have hzero : ∀ x, act 0 x = 1 := fun x ↦ by
    have := hadd 0 0 x
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hnat : ∀ (n : ℕ) x, act (n : O) x = x ^ n := fun n x ↦ by
    induction n with
    | zero => simp [hzero]
    | succ n ih => rw [Nat.cast_succ, hadd, ih, hone, pow_succ]
  let f : (Fin 2 → G) → (O × O →+ Additive G) := fun r ↦ AddMonoidHom.mk'
    (fun c ↦ Additive.ofMul (act c.1 (r 0) * act c.2 (r 1))) (fun c d ↦ by
      rw [← ofMul_mul, Prod.fst_add, Prod.snd_add, hadd, hadd, _root_.mul_mul_mul_comm])
  let I : AddSubgroup O := (Ideal.span {(N : O)}).toAddSubgroup
  have hker : ∀ r : Fin 2 → G, (∀ i, r i ^ N = 1) →
      (∀ a b, act a (r 0) * act b (r 1) = 1 → (N : O) ∣ a ∧ (N : O) ∣ b) → (f r).ker = I.prod I := by
    intro r hr ir
    ext ⟨a, b⟩
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_prod]
    change act a (r 0) * act b (r 1) = 1 ↔ a ∈ Ideal.span {(N : O)} ∧ b ∈ Ideal.span {(N : O)}
    rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    refine ⟨ir a b, ?_⟩
    rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    rw [hmul, hmul, hnat, hnat, hr, hr, map_one, map_one, _root_.one_mul]
  have hI : I.index ≠ 0 := by
    have : Finite (O ⧸ I) := ‹Finite (O ⧸ Ideal.span {(N : O)})›
    exact AddSubgroup.index_ne_zero_of_finite
  have cp : Nat.card (f p).range = I.index * I.index := by
    rw [← AddSubgroup.index_ker, hker p hp ip, AddSubgroup.index_prod]
  have cq : Nat.card (f q).range = I.index * I.index := by
    rw [← AddSubgroup.index_ker, hker q hq iq, AddSubgroup.index_prod]
  have : Finite (f q).range := Nat.finite_of_card_ne_zero (cq ▸ mul_ne_zero hI hI)
  have hle : (f p).range ≤ (f q).range := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    obtain ⟨c, d, h⟩ := sq (act a (p 0) * act b (p 1)) (by
      rw [mul_pow, ← map_pow, ← map_pow, hp, hp, map_one, map_one, _root_.one_mul])
    exact ⟨(c, d), congrArg Additive.ofMul h.symm⟩
  have heq := AddSubgroup.eq_of_le_of_card_ge hle (by rw [cp, cq])
  intro y hy
  obtain ⟨c, d, h⟩ := sq y hy
  have hm : Additive.ofMul y ∈ (f p).range := heq ▸ ⟨(c, d), congrArg Additive.ofMul h.symm⟩
  obtain ⟨⟨a, b⟩, hab⟩ := hm
  exact ⟨a, b, (congrArg Additive.toMul hab).symm⟩

/- English proof (translation)
Introduce `F _ _ _ 𝔠 N K _ _ hN X`. Take `⟨p, hp, ip, -⟩ : ∃ p : Fin 2 → (𝟙_ (Over (Sp K)) ⟶ X.A), (∀ i, p i ^ N = 1) ∧ (∀ a b : 𝓞 F, (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧ ∀ y : 𝟙_ (Over (Sp K)) ⟶ X.A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b)` from `hT F 𝔠 (Sp K) X N K (𝟙 _) hN`. Establish `inj : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (a b : 𝓞 F), (toUnit (Over.mk t) ≫ p 0 ≫ X.rm.act a) * (toUnit (Over.mk t) ≫ p 1 ≫ X.rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b`. Introduce `Ω _ _ t a b h`. Apply `ip` to reduce the goal to its premises.

Rewrite `h` using `[← MonObj.comp_mul, ← MonObj.comp_one (toUnit (Over.mk t))]`. Establish `ht : (toUnit (Over.mk t)).left = t` using `by simpa using Over.w (toUnit (Over.mk t))`. Establish `: Epi t` using `inferInstance`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Establish `h'` using `congrArg (fun z ↦ z.left) h`.

Simplify using `only [Over.comp_left, ht] at h'`. Conclude with `(cancel_epi t).1 h'`. Use `⟨⟨p, hp, inj, fun Ω _ _ t ↦ ?_⟩⟩` and prove the remaining obligations. Establish `hNΩ : (N : Ω) ≠ 0`. Use `(Spec.preimage t).hom.injective.ne hN` as an intermediate fact.

Simplify using `using this`. Establish `hN0 : (N : 𝓞 F) ≠ 0`. Establish `: N ≠ 0` using `by rintro rfl; simp at hN`. Conclude with `this` after adjusting the coercions. Take `⟨q, hq, iq, sq⟩` from `hT F 𝔠 (Sp K) X N Ω t hNΩ`.

Establish `: Finite (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)})` using `Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN0)`. Set `act : 𝓞 F → (Over.mk t ⟶ X.A) →* (Over.mk t ⟶ X.A)` to `fun a ↦ haveI := X.rm.hom a { toFun := fun y ↦ y ≫ X.rm.act a map_one' := MonObj.one_comp _ map_mul' := fun x y ↦ MonObj.mul_comp _ _ _ }`. Establish `key` using `span_torsion_of_indep N act (fun x ↦ by simp [act, X.rm.one]) (fun a b x ↦ by simp [act, X.rm.mul]) (fun a b x ↦ by simp [act, X.rm.add, MonObj.comp_mul]) (fun i ↦ toUnit (Over.mk t) ≫ p i) q (fun i ↦ by rw [← MonObj.comp_pow, hp, MonObj.comp_one]) hq (fun a b h ↦ inj Ω t a b (by …`. Introduce `y hy`. Take `⟨a, b, h⟩` from `key y hy`.

Conclude with `⟨a, b, by simpa [act] using h⟩`.
-/
theorem nonempty_level_of_torsion_basis (hT : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (S : Scheme.{0}) (X : Obj F 𝔠 S)
    (N : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), (N : Ω) ≠ 0 →
    ∃ p : Fin 2 → (Over.mk t ⟶ X.A), (∀ i, p i ^ N = 1) ∧
      (∀ a b : 𝓞 F, (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : Over.mk t ⟶ X.A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b)) :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ) (K : Type) [Field K] [IsAlgClosed K],
    (N : K) ≠ 0 → ∀ X : Obj F 𝔠 (Sp K), Nonempty (X.Level N) := by
  intro F _ _ _ 𝔠 N K _ _ hN X
  obtain ⟨p, hp, ip, -⟩ : ∃ p : Fin 2 → (𝟙_ (Over (Sp K)) ⟶ X.A), (∀ i, p i ^ N = 1) ∧
      (∀ a b : 𝓞 F, (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : 𝟙_ (Over (Sp K)) ⟶ X.A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) :=
    hT F 𝔠 (Sp K) X N K (𝟙 _) hN
  have inj : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (a b : 𝓞 F),
      (toUnit (Over.mk t) ≫ p 0 ≫ X.rm.act a) * (toUnit (Over.mk t) ≫ p 1 ≫ X.rm.act b) = 1 →
        (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
    intro Ω _ _ t a b h
    apply ip
    rw [← MonObj.comp_mul, ← MonObj.comp_one (toUnit (Over.mk t))] at h
    have ht : (toUnit (Over.mk t)).left = t := by simpa using Over.w (toUnit (Over.mk t))
    have : Epi t := inferInstance
    apply Over.OverMorphism.ext
    have h' := congrArg (fun z ↦ z.left) h
    simp only [Over.comp_left, ht] at h'
    exact (cancel_epi t).1 h'
  refine ⟨⟨p, hp, inj, fun Ω _ _ t ↦ ?_⟩⟩
  have hNΩ : (N : Ω) ≠ 0 := by
    have := (Spec.preimage t).hom.injective.ne hN
    simpa using this
  have hN0 : (N : 𝓞 F) ≠ 0 := by
    have : N ≠ 0 := by rintro rfl; simp at hN
    exact_mod_cast this
  obtain ⟨q, hq, iq, sq⟩ := hT F 𝔠 (Sp K) X N Ω t hNΩ
  have : Finite (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN0)
  let act : 𝓞 F → (Over.mk t ⟶ X.A) →* (Over.mk t ⟶ X.A) := fun a ↦
    haveI := X.rm.hom a
    { toFun := fun y ↦ y ≫ X.rm.act a
      map_one' := MonObj.one_comp _
      map_mul' := fun x y ↦ MonObj.mul_comp _ _ _ }
  have key := span_torsion_of_indep N act (fun x ↦ by simp [act, X.rm.one])
    (fun a b x ↦ by simp [act, X.rm.mul]) (fun a b x ↦ by simp [act, X.rm.add, MonObj.comp_mul])
    (fun i ↦ toUnit (Over.mk t) ≫ p i) q
    (fun i ↦ by rw [← MonObj.comp_pow, hp, MonObj.comp_one]) hq
    (fun a b h ↦ inj Ω t a b (by simpa [act] using h)) iq sq
  intro y hy
  obtain ⟨a, b, h⟩ := key y hy
  exact ⟨a, b, by simpa [act] using h⟩

end GlobalTheory.RealMult
