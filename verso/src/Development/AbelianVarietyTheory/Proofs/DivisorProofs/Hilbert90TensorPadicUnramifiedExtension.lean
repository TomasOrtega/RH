import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearFixedSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobQFixedMemRange
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

section HilbertNinety

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_inv]`.
-/
theorem iterate_groupEndomorphism_inv_apply {H : Type*} [Group H] (θ : H →* H) (i : ℕ) (x : H) :
    (⇑θ)^[i] x⁻¹ = ((⇑θ)^[i] x)⁻¹ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_inv]

/- English proof (translation)
Simplify using `[nrmG, List.range_succ, List.map_append, List.prod_append]`.
-/
theorem twistedNormProductIterate_succ_mul_iterate {H : Type} [Group H] (θ : H →* H) (n : ℕ) (δ : H) :
    nrmG θ (n + 1) δ = nrmG θ n δ * (⇑θ)^[n] δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => rfl`. Consider the case `succ n ih`. Apply the tactic sequence `rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Units.coe_map, ← ih] <;> rfl`.
-/
theorem units_map_ringHom_iterate_val {A : Type*} [CommRing A] (f : A →+* A) (i : ℕ) (u : Aˣ) :
    (((⇑(Units.map f.toMonoidHom))^[i] u : Aˣ) : A) = (⇑f)^[i] (u : A) := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Units.coe_map, ← ih] <;> rfl

/- English proof (translation)
Proceed by induction on `i generalizing v with`. Consider the case `zero => simp [nrmG]`. Consider the case `succ n ih`. Simplify using `only [Function.iterate_succ_apply]`. Rewrite using `[ih, twistedNormProductIterate_succ_mul_iterate, _root_.mul_inv_rev, Units.val_mul, ← iterate_groupEndomorphism_inv_apply, units_map_ringHom_iterate_val, ← RingHom.coe_pow, map_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem iterate_twisted_ringHom_mul_inv_eq_norm {A : Type} [CommRing A] (f : A →+* A) (a : Aˣ) (i : ℕ) (v : A) :
    (fun x => f x * ((a⁻¹ : Aˣ) : A))^[i] v =
      (⇑f)^[i] v * (((nrmG (Units.map f.toMonoidHom) i a)⁻¹ : Aˣ) : A) := by
  induction i generalizing v with
  | zero => simp [nrmG]
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    rw [ih, twistedNormProductIterate_succ_mul_iterate, _root_.mul_inv_rev, Units.val_mul, ← iterate_groupEndomorphism_inv_apply, units_map_ringHom_iterate_val,
      ← RingHom.coe_pow, map_mul]
    ring

variable (p : ℕ) [Fact p.Prime]

/- English proof (translation)
Proceed by induction on `i generalizing y with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [pow_succ, AlgEquiv.mul_apply, ih, Function.iterate_succ_apply] <;> rfl`.
-/
theorem unramifiedPadicFrobeniusAlgEquiv_pow_apply_eq_iterate (r : ℕ) (hr : 0 < r) (i : ℕ) (y : Qr p r) :
    (frobQEquiv p r hr ^ i) y = (⇑(frobQ p r))^[i] y := by
  induction i generalizing y with
  | zero => rfl
  | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, ih, Function.iterate_succ_apply] <;> rfl

/- English proof (translation)
Establish `h1 : frobQEquiv p r hr ^ r = 1`. Use `pow_orderOf_eq_one (frobQEquiv p r hr)` as an intermediate fact. Rewrite `this` using `[orderOf_frobQEquiv]`. Then use the resulting hypothesis. Rewrite using `[← unramifiedPadicFrobeniusAlgEquiv_pow_apply_eq_iterate p r hr, h1]`. Both sides reduce to the same expression.
-/
theorem padicUnramifiedFrobenius_iterate_degree_apply_eq (r : ℕ) (hr : 0 < r) (y : Qr p r) : (⇑(frobQ p r))^[r] y = y := by
  have h1 : frobQEquiv p r hr ^ r = 1 := by
    have := pow_orderOf_eq_one (frobQEquiv p r hr)
    rwa [orderOf_frobQEquiv] at this
  rw [← unramifiedPadicFrobeniusAlgEquiv_pow_apply_eq_iterate p r hr, h1]
  rfl

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h1 : frobQEquiv p r hr ^ i = 1` using `AlgEquiv.ext fun y => by`. Rewrite using `[unramifiedPadicFrobeniusAlgEquiv_pow_apply_eq_iterate, h y]`. Both sides reduce to the same expression.

Establish `h2` using `orderOf_dvd_of_pow_eq_one h1`. Rewrite `h2` using `[orderOf_frobQEquiv]`. Conclude with `absurd (Nat.le_of_dvd hi0 h2) (not_le.2 hir)`.
-/
theorem exists_ne_padicUnramifiedFrobenius_iterate_lt_degree (r : ℕ) (hr : 0 < r) (i : ℕ) (hi0 : 0 < i) (hir : i < r) :
    ∃ y : Qr p r, (⇑(frobQ p r))^[i] y ≠ y := by
  by_contra h
  push_neg at h
  have h1 : frobQEquiv p r hr ^ i = 1 := AlgEquiv.ext fun y => by
    rw [unramifiedPadicFrobeniusAlgEquiv_pow_apply_eq_iterate, h y]; rfl
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_frobQEquiv] at h2
  exact absurd (Nat.le_of_dvd hi0 h2) (not_le.2 hir)

variable (B : Type) [CommRing B] [Algebra ℚ_[p] B]

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => rfl`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply', ih, Function.iterate_succ_apply']`. Simplify using the standard rewrite rules.
-/
theorem tensorMap_padicUnramifiedFrobenius_iterate_tmul (r i : ℕ) (b : B) (y : Qr p r) :
    (⇑(Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)))^[i] (b ⊗ₜ y) =
      b ⊗ₜ (⇑(frobQ p r))^[i] y := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom ^ r) x = x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact map_zero _`. Consider the case `tmul b y`. Rewrite using `[RingHom.coe_pow]`.

Conclude with `(tensorMap_padicUnramifiedFrobenius_iterate_tmul p B r r b y).trans (by rw [padicUnramifiedFrobenius_iterate_degree_apply_eq p r hr])`. Consider the case `add x y hx hy => rw [map_add, hx, hy]`.
-/
theorem tensorMap_padicUnramifiedFrobenius_iterate_degree (r : ℕ) (hr : 0 < r) (x : B ⊗[ℚ_[p]] Qr p r) :
    (⇑(Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)))^[r] x = x := by
  change ((Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom ^ r) x = x
  induction x using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul b y =>
    rw [RingHom.coe_pow]
    exact (tensorMap_padicUnramifiedFrobenius_iterate_tmul p B r r b y).trans (by rw [padicUnramifiedFrobenius_iterate_degree_apply_eq p r hr])
  | add x y hx hy => rw [map_add, hx, hy]

end HilbertNinety

end GlobalTheory.LKMid

namespace GlobalTheory.LKMid

/- English proof (translation)
Introduce `p _ r hr B _ _ _ a ha`. Use `haveI : FiniteDimensional ℚ_[p] (Qr p r) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr`. Set `σ` to `Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)`. Set `τ : B ⊗[ℚ_[p]] Qr p r → B ⊗[ℚ_[p]] Qr p r` to `fun x => σ x * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _)`. Establish `hτr : ∀ v, τ^[r] v = v`.

Introduce `v`. Use `iterate_twisted_ringHom_mul_inv_eq_norm σ.toRingHom a r v` as an intermediate fact. Rewrite `this` using `[ha, inv_one, Units.val_one, mul_one]`. Conclude with `this.trans (tensorMap_padicUnramifiedFrobenius_iterate_degree p B r hr v)`. Set `W : Submodule ℚ_[p] (B ⊗[ℚ_[p]] Qr p r)` to `{ carrier := {v | τ v = v} add_mem' := by`.

Introduce `x y hx hy`. Use `show σ (x + y) * _ = x + y`. Rewrite using `[map_add, add_mul]`. Rewrite using `[show σ x * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = x from hx, show σ y * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = y from hy]`. Use the proof step `zero_mem' := by show σ 0 * _ = 0`.

Rewrite using `[map_zero, zero_mul]`. Use the proof step `smul_mem' := by`. Introduce `c x hx`. Use `show σ (c • x) * _ = c • x`. Rewrite using `[map_smul, smul_mul_assoc]`.

Rewrite using `[show σ x * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = x from hx] }`. Set `e : (Qr p r ⊗[ℚ_[p]] B) ≃ₐ[ℚ_[p]] (B ⊗[ℚ_[p]] Qr p r)` to `Algebra.TensorProduct.comm ℚ_[p] (Qr p r) B`. Establish `he_smul : ∀ (c : Qr p r) (w : Qr p r ⊗[ℚ_[p]] B), e (c • w) = ((1 : B) ⊗ₜ c) * e w`. Introduce `c w`. Apply the tactic sequence `rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.comm_tmul] <;> rfl`.

Set `s : Qr p r ≃+* Qr p r` to `(frobQEquiv p r hr).toRingEquiv`. Establish `hs : ∀ y, s y = frobQ p r y` using `fun _ => rfl`. Set `F : (Qr p r ⊗[ℚ_[p]] B) →+ (Qr p r ⊗[ℚ_[p]] B)` to `{ toFun := fun w => e.symm (τ (e w)) map_zero' := by simp [τ] map_add' := fun x y => by simp only [τ, map_add, add_mul] }`. Establish `hFe : ∀ w, e (F w) = τ (e w)` using `fun w => AlgEquiv.apply_symm_apply e _`. Establish `hF : ∀ (c : Qr p r) (w : Qr p r ⊗[ℚ_[p]] B), F (c • w) = s c • F w`.

Introduce `c w`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[hFe, he_smul, he_smul, hFe, hs]`. Simplify using `only [τ, σ, map_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, mul_assoc]`. Establish `hFi : ∀ (i : ℕ) (w : Qr p r ⊗[ℚ_[p]] B), F^[i] w = e.symm (τ^[i] (e w))`.

Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro w`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Introduce `w`. Rewrite using `[Function.iterate_succ_apply', ih, Function.iterate_succ_apply']`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[hFe, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]`. Establish `hFr : ∀ w, F^[r] w = w`.

Introduce `w`. Rewrite using `[hFi, hτr, AlgEquiv.symm_apply_apply]`. Establish `hsr : ∀ x, (⇑s)^[r] x = x` using `fun x => padicUnramifiedFrobenius_iterate_degree_apply_eq p r hr x`. Establish `hsi : ∀ i, 0 < i → i < r → ∃ x, (⇑s)^[i] x ≠ x` using `fun i h0 h1 => exists_ne_padicUnramifiedFrobenius_iterate_lt_degree p r hr i h0 h1`. Establish `hspan` using `GlobalTheory.semilinear_fixed_span (Qr p r) s r hr hsr hsi (Qr p r ⊗[ℚ_[p]] B) F hF hFr`.

Establish `hkey : ∀ m : Ideal (B ⊗[ℚ_[p]] Qr p r), m.IsMaximal → ∃ w ∈ W, w ∉ m`. Introduce `m hm`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Set `I' : Submodule (Qr p r) (Qr p r ⊗[ℚ_[p]] B)` to `{ carrier := {v | e v ∈ m} add_mem' := by`.

Introduce `x y hx hy`. Use `show e (x + y) ∈ m`. Rewrite using `[map_add]`. Conclude with `m.add_mem hx hy`. Use the proof step `zero_mem' := by show e 0 ∈ m`.

Rewrite using `[map_zero]`. Conclude with `m.zero_mem`. Use the proof step `smul_mem' := by`. Introduce `c x hx`. Use `show e (c • x) ∈ m`.

Rewrite using `[he_smul]`. Conclude with `m.mul_mem_left _ hx }`. Establish `hle : Submodule.span (Qr p r) {v | F v = v} ≤ I'`. Rewrite using `[Submodule.span_le]`. Introduce `v hv`.

Establish `hv' : τ (e v) = e v`. Establish `h2 : e (F v) = e v` using `congrArg e hv`. Rewrite `h2` using `[hFe]`. Then use the resulting hypothesis. Conclude with `h _ hv'`. Rewrite `hle` using `[hspan]`.

Establish `h1 : e 1 ∈ m` using `hle Submodule.mem_top`. Rewrite `h1` using `[map_one]`. Conclude with `hm.ne_top ((Ideal.eq_top_iff_one m).2 h1)`. Use `haveI : IsArtinianRing (B ⊗[ℚ_[p]] Qr p r) := IsArtinianRing.of_finite ℚ_[p] (B ⊗[ℚ_[p]] Qr p r)`. Establish `hfin` using `IsArtinianRing.setOf_isMaximal_finite (B ⊗[ℚ_[p]] Qr p r)`.

Set `fS : Ideal (B ⊗[ℚ_[p]] Qr p r) → Subspace ℚ_[p] W` to `fun I => (I.restrictScalars ℚ_[p]).comap W.subtype`. Establish `htop : (⊤ : Subspace ℚ_[p] W) ∉ hfin.toFinset.image fS`. Introduce `hmem`. Rewrite `hmem` using `[Finset.mem_image]`. Take `⟨I, hI, hIt⟩` from `hmem`.

Rewrite `hI` using `[Set.Finite.mem_toFinset]`. Take `⟨w, hwW, hwI⟩` from `hkey I hI`. Establish `: (⟨w, hwW⟩ : W) ∈ fS I` using `by rw [hIt]; exact Submodule.mem_top`. Conclude with `hwI this`. Take `⟨w, hw⟩` from `(Set.ne_univ_iff_exists_notMem _).1 (Subspace.biUnion_ne_univ_of_top_notMem htop)`.

Establish `hunit : IsUnit (w : B ⊗[ℚ_[p]] Qr p r)`. Assume the negation of the conclusion as `hu`. Take `⟨I, hI, hwI⟩` from `exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hu)`. Apply `hw` to reduce the goal to its premises. Rewrite using `[Set.mem_iUnion₂]`.

Conclude with `⟨fS I, Finset.mem_image.2 ⟨I, (Set.Finite.mem_toFinset _).2 hI, rfl⟩, hwI⟩`. Establish `hfix : σ (w : B ⊗[ℚ_[p]] Qr p r) * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = w` using `w.2`. Establish `hσ : σ (hunit.unit : B ⊗[ℚ_[p]] Qr p r) = (hunit.unit : B ⊗[ℚ_[p]] Qr p r) * a`. Rewrite using `[IsUnit.unit_spec]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc, Units.inv_mul, mul_one]`. Use `_ = w * a := by rw [hfix]`. Use `⟨hunit.unit, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.coe_map]`. Use `show (a : B ⊗[ℚ_[p]] Qr p r) = _ * σ _`.

Rewrite using `[hσ, Units.inv_mul_cancel_left]`.
-/
theorem hilbert90_frobenius_tensor_unramified_padic : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ (B : Type) [CommRing B] [Algebra ℚ_[p] B]
    [Module.Finite ℚ_[p] B] (a : (B ⊗[ℚ_[p]] Qr p r)ˣ),
    nrmG (Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom.toMonoidHom) r a = 1 →
    ∃ g : (B ⊗[ℚ_[p]] Qr p r)ˣ, a = g⁻¹ *
      Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom.toMonoidHom g := by
  intro p _ r hr B _ _ _ a ha
  haveI : FiniteDimensional ℚ_[p] (Qr p r) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr
  let σ := Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)
  let τ : B ⊗[ℚ_[p]] Qr p r → B ⊗[ℚ_[p]] Qr p r := fun x => σ x * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _)
  have hτr : ∀ v, τ^[r] v = v := by
    intro v
    have := iterate_twisted_ringHom_mul_inv_eq_norm σ.toRingHom a r v
    rw [ha, inv_one, Units.val_one, mul_one] at this
    exact this.trans (tensorMap_padicUnramifiedFrobenius_iterate_degree p B r hr v)

  let W : Submodule ℚ_[p] (B ⊗[ℚ_[p]] Qr p r) :=
    { carrier := {v | τ v = v}
      add_mem' := by
        intro x y hx hy
        show σ (x + y) * _ = x + y
        rw [map_add, add_mul]
        rw [show σ x * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = x from hx,
          show σ y * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = y from hy]
      zero_mem' := by
        show σ 0 * _ = 0
        rw [map_zero, zero_mul]
      smul_mem' := by
        intro c x hx
        show σ (c • x) * _ = c • x
        rw [map_smul, smul_mul_assoc]
        rw [show σ x * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = x from hx] }

  let e : (Qr p r ⊗[ℚ_[p]] B) ≃ₐ[ℚ_[p]] (B ⊗[ℚ_[p]] Qr p r) := Algebra.TensorProduct.comm ℚ_[p] (Qr p r) B
  have he_smul : ∀ (c : Qr p r) (w : Qr p r ⊗[ℚ_[p]] B), e (c • w) = ((1 : B) ⊗ₜ c) * e w := by
    intro c w
    rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.comm_tmul] <;> rfl
  let s : Qr p r ≃+* Qr p r := (frobQEquiv p r hr).toRingEquiv
  have hs : ∀ y, s y = frobQ p r y := fun _ => rfl
  let F : (Qr p r ⊗[ℚ_[p]] B) →+ (Qr p r ⊗[ℚ_[p]] B) :=
    { toFun := fun w => e.symm (τ (e w))
      map_zero' := by simp [τ]
      map_add' := fun x y => by simp only [τ, map_add, add_mul] }
  have hFe : ∀ w, e (F w) = τ (e w) := fun w => AlgEquiv.apply_symm_apply e _
  have hF : ∀ (c : Qr p r) (w : Qr p r ⊗[ℚ_[p]] B), F (c • w) = s c • F w := by
    intro c w
    apply e.injective
    rw [hFe, he_smul, he_smul, hFe, hs]
    simp only [τ, σ, map_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, mul_assoc]
  have hFi : ∀ (i : ℕ) (w : Qr p r ⊗[ℚ_[p]] B), F^[i] w = e.symm (τ^[i] (e w)) := by
    intro i
    induction i with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      apply e.injective
      rw [hFe, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  have hFr : ∀ w, F^[r] w = w := by
    intro w
    rw [hFi, hτr, AlgEquiv.symm_apply_apply]
  have hsr : ∀ x, (⇑s)^[r] x = x := fun x => padicUnramifiedFrobenius_iterate_degree_apply_eq p r hr x
  have hsi : ∀ i, 0 < i → i < r → ∃ x, (⇑s)^[i] x ≠ x := fun i h0 h1 => exists_ne_padicUnramifiedFrobenius_iterate_lt_degree p r hr i h0 h1
  have hspan := GlobalTheory.semilinear_fixed_span (Qr p r) s r hr hsr hsi (Qr p r ⊗[ℚ_[p]] B) F hF hFr

  have hkey : ∀ m : Ideal (B ⊗[ℚ_[p]] Qr p r), m.IsMaximal → ∃ w ∈ W, w ∉ m := by
    intro m hm
    by_contra h
    push_neg at h
    let I' : Submodule (Qr p r) (Qr p r ⊗[ℚ_[p]] B) :=
      { carrier := {v | e v ∈ m}
        add_mem' := by
          intro x y hx hy
          show e (x + y) ∈ m
          rw [map_add]
          exact m.add_mem hx hy
        zero_mem' := by
          show e 0 ∈ m
          rw [map_zero]
          exact m.zero_mem
        smul_mem' := by
          intro c x hx
          show e (c • x) ∈ m
          rw [he_smul]
          exact m.mul_mem_left _ hx }
    have hle : Submodule.span (Qr p r) {v | F v = v} ≤ I' := by
      rw [Submodule.span_le]
      intro v hv
      have hv' : τ (e v) = e v := by
        have h2 : e (F v) = e v := congrArg e hv
        rwa [hFe] at h2
      exact h _ hv'
    rw [hspan] at hle
    have h1 : e 1 ∈ m := hle Submodule.mem_top
    rw [map_one] at h1
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 h1)
  haveI : IsArtinianRing (B ⊗[ℚ_[p]] Qr p r) := IsArtinianRing.of_finite ℚ_[p] (B ⊗[ℚ_[p]] Qr p r)
  have hfin := IsArtinianRing.setOf_isMaximal_finite (B ⊗[ℚ_[p]] Qr p r)
  let fS : Ideal (B ⊗[ℚ_[p]] Qr p r) → Subspace ℚ_[p] W := fun I => (I.restrictScalars ℚ_[p]).comap W.subtype
  have htop : (⊤ : Subspace ℚ_[p] W) ∉ hfin.toFinset.image fS := by
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨I, hI, hIt⟩ := hmem
    rw [Set.Finite.mem_toFinset] at hI
    obtain ⟨w, hwW, hwI⟩ := hkey I hI
    have : (⟨w, hwW⟩ : W) ∈ fS I := by rw [hIt]; exact Submodule.mem_top
    exact hwI this
  obtain ⟨w, hw⟩ := (Set.ne_univ_iff_exists_notMem _).1 (Subspace.biUnion_ne_univ_of_top_notMem htop)
  have hunit : IsUnit (w : B ⊗[ℚ_[p]] Qr p r) := by
    by_contra hu
    obtain ⟨I, hI, hwI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hu)
    apply hw
    rw [Set.mem_iUnion₂]
    exact ⟨fS I, Finset.mem_image.2 ⟨I, (Set.Finite.mem_toFinset _).2 hI, rfl⟩, hwI⟩
  have hfix : σ (w : B ⊗[ℚ_[p]] Qr p r) * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = w := w.2
  have hσ : σ (hunit.unit : B ⊗[ℚ_[p]] Qr p r) = (hunit.unit : B ⊗[ℚ_[p]] Qr p r) * a := by
    rw [IsUnit.unit_spec]
    calc σ (w : B ⊗[ℚ_[p]] Qr p r)
        = σ (w : B ⊗[ℚ_[p]] Qr p r) * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) * a := by
          rw [mul_assoc, Units.inv_mul, mul_one]
      _ = w * a := by rw [hfix]
  refine ⟨hunit.unit, Units.ext ?_⟩
  rw [Units.val_mul, Units.coe_map]
  show (a : B ⊗[ℚ_[p]] Qr p r) = _ * σ _
  rw [hσ, Units.inv_mul_cancel_left]

end GlobalTheory.LKMid
