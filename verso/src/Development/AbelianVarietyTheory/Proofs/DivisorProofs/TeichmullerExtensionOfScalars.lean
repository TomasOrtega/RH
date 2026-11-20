import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain

set_option autoImplicit false

open GlobalTheory.RingChain
open scoped TensorProduct Pointwise ChangeOfRings

namespace GlobalTheory.RingChain

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `h0 : Ideal.Quotient.mk (Ideal.span {(p : R)}) (p : R) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)`. Set `f : R →+* R ⧸ Ideal.span {(p : R)}` to `{ toFun := fun a => Ideal.Quotient.mk _ (a ^ p ^ k) map_one' := by simp map_mul' := fun a b => by rw [mul_pow, map_mul] map_zero' := by rw [zero_pow (pow_ne_zero _ hp.ne_zero), map_zero] map_add' := fun a b => by`. Take `⟨r, hr⟩` from `exists_add_pow_prime_pow_eq hp a b k`. Rewrite using `[hr, map_add, map_add, mul_assoc, mul_assoc, map_mul, h0, zero_mul, add_zero] }`.

Use `⟨Ideal.Quotient.lift _ f fun x hx => ?_, fun _ => rfl⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton.1 hx`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ _ = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, mul_pow, Ideal.mem_span_singleton]`. Conclude with `hg.mul_right _`.
-/
theorem exists_powFrob_quot (p k : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (g : R) (hg : (p : R) ∣ g ^ p ^ k) :
    ∃ F : (R ⧸ Ideal.span {g}) →+* R ⧸ Ideal.span {(p : R)},
      ∀ a, F (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (a ^ p ^ k) := by
  have hp : p.Prime := Fact.out
  have h0 : Ideal.Quotient.mk (Ideal.span {(p : R)}) (p : R) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  let f : R →+* R ⧸ Ideal.span {(p : R)} :=
    { toFun := fun a => Ideal.Quotient.mk _ (a ^ p ^ k)
      map_one' := by simp
      map_mul' := fun a b => by rw [mul_pow, map_mul]
      map_zero' := by rw [zero_pow (pow_ne_zero _ hp.ne_zero), map_zero]
      map_add' := fun a b => by
        obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp a b k
        rw [hr, map_add, map_add, mul_assoc, mul_assoc, map_mul, h0, zero_mul, add_zero] }
  refine ⟨Ideal.Quotient.lift _ f fun x hx => ?_, fun _ => rfl⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hx
  change Ideal.Quotient.mk _ _ = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, mul_pow, Ideal.mem_span_singleton]
  exact hg.mul_right _

/- English proof (translation)
Take `⟨F, hF⟩` from `exists_powFrob_quot p k g hg`. Establish `sm : ∀ (a : R) (z : P ⧸ (p : R) • (⊤ : Submodule R P)), (Ideal.Quotient.mk (Ideal.span {(p : R)}) a) • z = a • z` using `fun _ _ => rfl`. Set `Y : ModuleCat R` to `(ModuleCat.restrictScalars s).obj (ModuleCat.of _ (R ⧸ Ideal.span {g}))`. Set `c : R → Y` to `fun r => (Ideal.Quotient.mk _ r : R ⧸ Ideal.span {g})`. Establish `csurj : ∀ b : Y, ∃ r, c r = b` using `fun b => Ideal.Quotient.mk_surjective (I := Ideal.span {g}) b`.

Establish `hc : ∀ r x a : R, s r = Ideal.Quotient.mk _ x → r • c a = c (x * a)` using `fun r x a h => by`. Express the relevant statement in the definitionally equal form `s r * Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ _`. Rewrite using `[h, map_mul]`. Set `e' : Y ⊗[R] P ≃+ M` to `e`. Establish `he' : ∀ r y, e' (c r ⊗ₜ y) = r • lam y` using `he`.

Set `F' : Y →+ R ⧸ Ideal.span {(p : R)}` to `F.toAddMonoidHom`. Establish `hF' : ∀ a, F' (c a) = Ideal.Quotient.mk _ (a ^ p ^ k)` using `hF`. Set `w : P →ₗ[R] P ⧸ (p : R) • (⊤ : Submodule R P)` to `(u : R) • Submodule.mkQ _`. Establish `hw : ∀ y, w y = Submodule.Quotient.mk ((u : R) • y)` using `fun _ => rfl`. Set `κ₀ : Y ⊗[R] P →+ P ⧸ (p : R) • (⊤ : Submodule R P)` to `TensorProduct.liftAddHom (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun y => F' b • w y) fun y y' => by rw [map_add, smul_add]) fun b b' => AddMonoidHom.ext fun y => by`.

Express the relevant statement in the definitionally equal form `F' (b + b') • w y = F' b • w y + F' b' • w y`. Rewrite using `[map_add, add_smul])`. Use `fun r b y => by`. Take `⟨a, rfl⟩` from `csurj b`. Take `⟨x, hx, hx'⟩` from `hs r`.

Express the relevant statement in the definitionally equal form `F' (r • c a) • w y = F' (c a) • w (r • y)`. Rewrite using `[hc r x a hx, hF', hF', mul_pow, map_mul, Ideal.Quotient.eq.2 hx', map_smul, ← sm r, ← mul_smul, mul_comm]`. Set `κ : M →+ P ⧸ (p : R) • (⊤ : Submodule R P)` to `κ₀.comp e'.symm.toAddMonoidHom`. Establish `hκ : ∀ a y, κ (a • lam y) = a ^ p ^ k • w y` using `fun a y => by`. Rewrite using `[← he', ← sm, ← hF']`.

Express the relevant statement in the definitionally equal form `κ₀ (e'.symm (e' _)) = _`. Rewrite using `[AddEquiv.symm_apply_apply]`. Both sides reduce to the same expression. Establish `hκ1 : ∀ y, κ (lam y) = w y` using `fun y => by`. Simplify using `using hκ 1 y`.

Establish `ind : ∀ Q : M → Prop, Q 0 → (∀ x y, Q x → Q y → Q (x + y)) → (∀ (a : R) y, Q (a • lam y)) → ∀ m, Q m`. Introduce `Q h0 ha ht m`. Take `⟨t, rfl⟩` from `e'.surjective m`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => rwa [map_zero]`.

Consider the case `add s t hs ht => rw [map_add]`. Conclude with `ha _ _ hs ht`. Consider the case `tmul b y`. Take `⟨a, rfl⟩` from `csurj b`. Rewrite using `[he']`.

Conclude with `ht a y`. Establish `hsl : ∀ (r : R) m, κ (r • m) = r ^ p ^ k • κ m` using `fun r => ind _ (by simp) (fun x y hx hy => by rw [smul_add, map_add, map_add, smul_add, hx, hy]) fun a y => by rw [← mul_smul, hκ, hκ, mul_pow, mul_smul]`. Use `⟨κ, hκ1, fun f hf => ?_⟩` and prove the remaining obligations. Set `X : ModuleCat R` to `(ModuleCat.restrictScalars f).obj (ModuleCat.of _ (R ⧸ Ideal.span {(p : R)}))`. Set `d : R → X` to `fun r => (Ideal.Quotient.mk _ r : R ⧸ Ideal.span {(p : R)})`.

Establish `dsurj : ∀ b : X, ∃ r, d r = b` using `fun b => Ideal.Quotient.mk_surjective (I := Ideal.span {(p : R)}) b`. Establish `hd : ∀ r a : R, r • d a = d (r ^ p ^ k * a)` using `fun r a => by`. Express the relevant statement in the definitionally equal form `f r * Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ _`. Rewrite using `[hf, map_mul]`. Set `i : X →+ R ⧸ Ideal.span {(p : R)}` to `AddMonoidHom.id _`.

Establish `hi : ∀ a, i (d a) = Ideal.Quotient.mk _ a` using `fun _ => rfl`. Set `v : X ⊗[R] M →+ P ⧸ (p : R) • (⊤ : Submodule R P)` to `TensorProduct.liftAddHom (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun m => i b • κ m) fun y y' => by rw [map_add, smul_add]) fun b b' => AddMonoidHom.ext fun m => by`. Express the relevant statement in the definitionally equal form `i (b + b') • κ m = i b • κ m + i b' • κ m`. Rewrite using `[map_add, add_smul])`. Use `fun r b m => by`.

Take `⟨a, rfl⟩` from `dsurj b`. Express the relevant statement in the definitionally equal form `i (r • d a) • κ m = i (d a) • κ (r • m)`. Rewrite using `[hd, hi, hi, sm, sm, hsl, ← mul_smul, mul_comm]`. Establish `hv : ∀ a m, v (d a ⊗ₜ m) = a • κ m` using `fun _ _ => rfl`. Establish `key : ∀ r y, (d 1 ⊗ₜ[R] lam (r • y) : X ⊗[R] M) = d r ⊗ₜ lam y` using `fun r y => by`.

Take `⟨x, hx, hx'⟩` from `hs r`. Establish `h1 : lam (r • y) = x • lam y`. Rewrite using `[← one_smul R (lam (r • y)), ← he', ← he', ← TensorProduct.smul_tmul, hc r x 1 hx, mul_one]`. Establish `h2 : d (x ^ p ^ k) = d r` using `Ideal.Quotient.eq.2 hx'`. Rewrite using `[h1, ← TensorProduct.smul_tmul, hd, mul_one, h2]`.

Establish `gen : ∀ t : X ⊗[R] M, ∃ y, t = d 1 ⊗ₜ lam y` using `fun t => by`. Establish `hz : ∃ y, (0 : X ⊗[R] M) = d 1 ⊗ₜ lam y` using `⟨0, by rw [map_zero, TensorProduct.tmul_zero]⟩`. Establish `ha : ∀ s t : X ⊗[R] M, (∃ y, s = d 1 ⊗ₜ lam y) → (∃ y, t = d 1 ⊗ₜ lam y) → ∃ y, s + t = d 1 ⊗ₜ lam y`. Introduce and unpack `_ _ ⟨y, rfl⟩ ⟨y', rfl⟩`. Conclude with `⟨y + y', by rw [map_add, TensorProduct.tmul_add]⟩`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact hz`. Consider the case `add s t hs ht => exact ha _ _ hs ht`. Consider the case `tmul b m`. Take `⟨a, rfl⟩` from `dsurj b`.

Use `ind (fun m => ∃ y, (d a ⊗ₜ[R] m : X ⊗[R] M) = d 1 ⊗ₜ lam y) ?_ (fun x y hx hy => ?_) (fun r y => ?_) m` and prove the remaining obligations. Simplify `hz` using `only [TensorProduct.tmul_zero]`. Simplify `ha _ _ hx hy` using `only [TensorProduct.tmul_add]`. Conclude with `⟨(r ^ p ^ k * a) • y, by rw [key, ← TensorProduct.smul_tmul, hd]⟩`. Establish `bij : Function.Bijective v`.

Use `⟨(injective_iff_map_eq_zero _).2 fun t ht => ?_, fun z => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `gen t`. Rewrite `ht` using `[hv, one_smul, hκ1, hw, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨z, -, hz⟩` from `ht`. Establish `hy : y = (p : R) • ((u⁻¹ : Rˣ) : R) • z`.

Rewrite using `[smul_comm, hz, ← mul_smul, Units.inv_mul, one_smul]`. Establish `h0 : d (p : R) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)`. Rewrite using `[hy, key, h0, TensorProduct.zero_tmul]`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Conclude with `⟨d 1 ⊗ₜ lam (((u⁻¹ : Rˣ) : R) • y), by`.

Rewrite using `[hv, one_smul, hκ1, hw, ← mul_smul, Units.mul_inv, one_smul]⟩`. Conclude with `⟨AddEquiv.ofBijective v bij, hv⟩`.
-/
theorem exists_isFrobLin_twist (p k : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (g : R) (u : Rˣ)
    (s : R →+* R ⧸ Ideal.span {g}) (hg : (p : R) ∣ g ^ p ^ k)
    (hs : ∀ r : R, ∃ x : R, s r = Ideal.Quotient.mk _ x ∧ x ^ p ^ k - r ∈ Ideal.span {(p : R)})
    (P M : Type) [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M] (lam : P →+ M)
    (e : (ModuleCat.extendScalars s).obj (ModuleCat.of R P) ≃+ M)
    (he : ∀ (r : R) (y : P), e ((Ideal.Quotient.mk _ r : R ⧸ Ideal.span {g}) ⊗ₜ[R, s] y) = r • lam y) :
    ∃ κ : M →+ P ⧸ (p : R) • (⊤ : Submodule R P),
      (∀ y, κ (lam y) = Submodule.Quotient.mk ((u : R) • y)) ∧ IsFrobLin R p (p ^ k) κ := by
  obtain ⟨F, hF⟩ := exists_powFrob_quot p k g hg
  have sm : ∀ (a : R) (z : P ⧸ (p : R) • (⊤ : Submodule R P)),
      (Ideal.Quotient.mk (Ideal.span {(p : R)}) a) • z = a • z := fun _ _ => rfl
  let Y : ModuleCat R := (ModuleCat.restrictScalars s).obj (ModuleCat.of _ (R ⧸ Ideal.span {g}))
  let c : R → Y := fun r => (Ideal.Quotient.mk _ r : R ⧸ Ideal.span {g})
  have csurj : ∀ b : Y, ∃ r, c r = b := fun b => Ideal.Quotient.mk_surjective (I := Ideal.span {g}) b
  have hc : ∀ r x a : R, s r = Ideal.Quotient.mk _ x → r • c a = c (x * a) := fun r x a h => by
    change s r * Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ _
    rw [h, map_mul]
  let e' : Y ⊗[R] P ≃+ M := e
  have he' : ∀ r y, e' (c r ⊗ₜ y) = r • lam y := he
  let F' : Y →+ R ⧸ Ideal.span {(p : R)} := F.toAddMonoidHom
  have hF' : ∀ a, F' (c a) = Ideal.Quotient.mk _ (a ^ p ^ k) := hF
  let w : P →ₗ[R] P ⧸ (p : R) • (⊤ : Submodule R P) := (u : R) • Submodule.mkQ _
  have hw : ∀ y, w y = Submodule.Quotient.mk ((u : R) • y) := fun _ => rfl
  let κ₀ : Y ⊗[R] P →+ P ⧸ (p : R) • (⊤ : Submodule R P) := TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun y => F' b • w y) fun y y' => by rw [map_add, smul_add])
      fun b b' => AddMonoidHom.ext fun y => by
        change F' (b + b') • w y = F' b • w y + F' b' • w y
        rw [map_add, add_smul])
    fun r b y => by
      obtain ⟨a, rfl⟩ := csurj b
      obtain ⟨x, hx, hx'⟩ := hs r
      change F' (r • c a) • w y = F' (c a) • w (r • y)
      rw [hc r x a hx, hF', hF', mul_pow, map_mul, Ideal.Quotient.eq.2 hx', map_smul, ← sm r, ← mul_smul, mul_comm]
  let κ : M →+ P ⧸ (p : R) • (⊤ : Submodule R P) := κ₀.comp e'.symm.toAddMonoidHom
  have hκ : ∀ a y, κ (a • lam y) = a ^ p ^ k • w y := fun a y => by
    rw [← he', ← sm, ← hF']
    change κ₀ (e'.symm (e' _)) = _
    rw [AddEquiv.symm_apply_apply]
    rfl
  have hκ1 : ∀ y, κ (lam y) = w y := fun y => by
    simpa using hκ 1 y
  have ind : ∀ Q : M → Prop, Q 0 → (∀ x y, Q x → Q y → Q (x + y)) → (∀ (a : R) y, Q (a • lam y)) → ∀ m, Q m := by
    intro Q h0 ha ht m
    obtain ⟨t, rfl⟩ := e'.surjective m
    induction t using TensorProduct.induction_on with
    | zero => rwa [map_zero]
    | add s t hs ht => rw [map_add]; exact ha _ _ hs ht
    | tmul b y =>
      obtain ⟨a, rfl⟩ := csurj b
      rw [he']; exact ht a y
  have hsl : ∀ (r : R) m, κ (r • m) = r ^ p ^ k • κ m := fun r => ind _ (by simp)
    (fun x y hx hy => by rw [smul_add, map_add, map_add, smul_add, hx, hy])
    fun a y => by rw [← mul_smul, hκ, hκ, mul_pow, mul_smul]
  refine ⟨κ, hκ1, fun f hf => ?_⟩
  let X : ModuleCat R := (ModuleCat.restrictScalars f).obj (ModuleCat.of _ (R ⧸ Ideal.span {(p : R)}))
  let d : R → X := fun r => (Ideal.Quotient.mk _ r : R ⧸ Ideal.span {(p : R)})
  have dsurj : ∀ b : X, ∃ r, d r = b := fun b => Ideal.Quotient.mk_surjective (I := Ideal.span {(p : R)}) b
  have hd : ∀ r a : R, r • d a = d (r ^ p ^ k * a) := fun r a => by
    change f r * Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ _
    rw [hf, map_mul]
  let i : X →+ R ⧸ Ideal.span {(p : R)} := AddMonoidHom.id _
  have hi : ∀ a, i (d a) = Ideal.Quotient.mk _ a := fun _ => rfl
  let v : X ⊗[R] M →+ P ⧸ (p : R) • (⊤ : Submodule R P) := TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun m => i b • κ m) fun y y' => by rw [map_add, smul_add])
      fun b b' => AddMonoidHom.ext fun m => by
        change i (b + b') • κ m = i b • κ m + i b' • κ m
        rw [map_add, add_smul])
    fun r b m => by
      obtain ⟨a, rfl⟩ := dsurj b
      change i (r • d a) • κ m = i (d a) • κ (r • m)
      rw [hd, hi, hi, sm, sm, hsl, ← mul_smul, mul_comm]
  have hv : ∀ a m, v (d a ⊗ₜ m) = a • κ m := fun _ _ => rfl
  have key : ∀ r y, (d 1 ⊗ₜ[R] lam (r • y) : X ⊗[R] M) = d r ⊗ₜ lam y := fun r y => by
    obtain ⟨x, hx, hx'⟩ := hs r
    have h1 : lam (r • y) = x • lam y := by
      rw [← one_smul R (lam (r • y)), ← he', ← he', ← TensorProduct.smul_tmul, hc r x 1 hx, mul_one]
    have h2 : d (x ^ p ^ k) = d r := Ideal.Quotient.eq.2 hx'
    rw [h1, ← TensorProduct.smul_tmul, hd, mul_one, h2]
  have gen : ∀ t : X ⊗[R] M, ∃ y, t = d 1 ⊗ₜ lam y := fun t => by
    have hz : ∃ y, (0 : X ⊗[R] M) = d 1 ⊗ₜ lam y := ⟨0, by rw [map_zero, TensorProduct.tmul_zero]⟩
    have ha : ∀ s t : X ⊗[R] M, (∃ y, s = d 1 ⊗ₜ lam y) → (∃ y, t = d 1 ⊗ₜ lam y) → ∃ y, s + t = d 1 ⊗ₜ lam y := by
      rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩
      exact ⟨y + y', by rw [map_add, TensorProduct.tmul_add]⟩
    induction t using TensorProduct.induction_on with
    | zero => exact hz
    | add s t hs ht => exact ha _ _ hs ht
    | tmul b m =>
      obtain ⟨a, rfl⟩ := dsurj b
      refine ind (fun m => ∃ y, (d a ⊗ₜ[R] m : X ⊗[R] M) = d 1 ⊗ₜ lam y) ?_ (fun x y hx hy => ?_) (fun r y => ?_) m
      · simpa only [TensorProduct.tmul_zero] using hz
      · simpa only [TensorProduct.tmul_add] using ha _ _ hx hy
      · exact ⟨(r ^ p ^ k * a) • y, by rw [key, ← TensorProduct.smul_tmul, hd]⟩
  have bij : Function.Bijective v := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun t ht => ?_, fun z => ?_⟩
    · obtain ⟨y, rfl⟩ := gen t
      rw [hv, one_smul, hκ1, hw, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at ht
      obtain ⟨z, -, hz⟩ := ht
      have hy : y = (p : R) • ((u⁻¹ : Rˣ) : R) • z := by
        rw [smul_comm, hz, ← mul_smul, Units.inv_mul, one_smul]
      have h0 : d (p : R) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      rw [hy, key, h0, TensorProduct.zero_tmul]
    · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      exact ⟨d 1 ⊗ₜ lam (((u⁻¹ : Rˣ) : R) • y), by
        rw [hv, one_smul, hκ1, hw, ← mul_smul, Units.mul_inv, one_smul]⟩
  exact ⟨AddEquiv.ofBijective v bij, hv⟩

end GlobalTheory.RingChain
