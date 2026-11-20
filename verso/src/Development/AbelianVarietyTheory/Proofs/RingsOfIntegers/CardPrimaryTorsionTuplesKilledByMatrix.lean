import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructureStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.InZhIffKillsAdapted
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight

set_option autoImplicit false

namespace GlobalTheory.TorsCount

/- English proof (translation)
Use `haveI := Fact.mk hℓ`. Set `P : Sylow ℓ (Multiplicative C)` to `⟨CommGroup.primaryComponent (Multiplicative C) ℓ, CommGroup.primaryComponent.isPGroup, fun {Q} hQ hle => le_antisymm (fun x hx => by`. Take `⟨k, hk⟩` from `hQ ⟨x, hx⟩`. Conclude with `CommGroup.mem_primaryComponent.2 ⟨k, congrArg Subtype.val hk⟩) hle⟩`. Establish `h` using `Sylow.card_eq_multiplicity P`.

Rewrite `h` using `[Nat.card_congr (Multiplicative.toAdd (α := C))]`. Rewrite using `[← h]`. Conclude with `Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd fun c => (CommGroup.mem_primaryComponent (G := Multiplicative C) (g := Multiplicative.ofAdd c)).symm)`.
-/
theorem card_primary (C : Type) [AddCommGroup C] [Finite C] (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Nat.card {c : C // ∃ j : ℕ, ℓ ^ j • c = 0} = ℓ ^ (Nat.card C).factorization ℓ := by
  haveI := Fact.mk hℓ
  let P : Sylow ℓ (Multiplicative C) :=
    ⟨CommGroup.primaryComponent (Multiplicative C) ℓ, CommGroup.primaryComponent.isPGroup, fun {Q} hQ hle =>
      le_antisymm (fun x hx => by
        obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
        exact CommGroup.mem_primaryComponent.2 ⟨k, congrArg Subtype.val hk⟩) hle⟩
  have h := Sylow.card_eq_multiplicity P
  rw [Nat.card_congr (Multiplicative.toAdd (α := C))] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd fun c =>
    (CommGroup.mem_primaryComponent (G := Multiplicative C) (g := Multiplicative.ofAdd c)).symm)

/- English proof (translation)
Take `⟨a, b, hab⟩` from `(Nat.isCoprime_iff_coprime.2 h)`. Use `⟨a, fun U _ u hu => ?_⟩` and prove the remaining obligations. Establish `: (a * k + b * m) • u = u` using `by rw [hab, one_smul]`. Rewrite `this` using `[add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, hu, smul_zero, add_zero]`. Then use the resulting hypothesis.
-/
theorem exists_inv {k m : ℕ} (h : Nat.Coprime k m) : ∃ a : ℤ, ∀ (U : Type) [AddCommGroup U] (u : U), m • u = 0 →
    a • k • u = u := by
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 h)
  refine ⟨a, fun U _ u hu => ?_⟩
  have : (a * k + b * m) • u = u := by rw [hab, one_smul]
  rwa [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, hu, smul_zero, add_zero] at this

/- English proof (translation)
Establish `hM0 : ∀ w, ev (M • w) = 0` using `fun w => (hker _).2 ⟨w, rfl⟩`. Set `φ : (W ⧸ LinearMap.range Q) →ₗ[ℤ] U` to `(LinearMap.range Q).liftQ (ev.toIntLinearMap ∘ₗ G) (by`. Introduce and unpack `_ ⟨w, rfl⟩`. Simplify using `only [LinearMap.mem_ker, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap]`. Rewrite using `[hGQ, mul_comm, mul_smul, hM0])`.

Establish `hφ : ∀ w, φ (Submodule.Quotient.mk w) = ev (G w)` using `fun w => rfl`. Establish `hφk : ∀ c, φ c = 0 → k • c = 0` using `fun c hc => by`. Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ c`. Take `⟨b, hb⟩` from `(hker _).1 ((hφ w).symm.trans hc)`. Establish `h1 : M • (k • w - Q b) = 0`.

Rewrite using `[smul_sub, smul_smul, mul_comm, ← hQG, hb, map_nsmul, sub_self]`. Establish `h2` using `sub_eq_zero.1 (tf M _ hM h1)`. Express the relevant statement in the definitionally equal form `(LinearMap.range Q).mkQ (k • w) = 0`. Rewrite using `[h2]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 ⟨b, rfl⟩`.

Use `symm`. Use `Nat.card_eq_of_bijective (fun c => ⟨φ c.1, ?_, ?_⟩) ⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `Submodule.Quotient.mk_surjective _ c.1`. Rewrite using `[← hw, hφ, hev, hQG, mul_comm, mul_smul, hM0]`. Take `⟨j, hj⟩` from `c.2`.

Conclude with `⟨j, by rw [← map_nsmul, hj, map_zero]⟩`. Introduce and unpack `⟨c, i, hi⟩ ⟨d, j, hj⟩ h`. Establish `h1 : φ (c - d) = 0` using `by rw [map_sub]; exact sub_eq_zero.2 (congrArg Subtype.val h)`. Take `⟨a, ha⟩` from `exists_inv (hk.pow_right (i + j))`. Establish `h2` using `ha _ (c - d) (by`.

Rewrite using `[smul_sub, pow_add, mul_smul _ _ d, hj, mul_comm, mul_smul, hi, smul_zero, smul_zero, sub_zero])`. Rewrite `h2` using `[hφk _ h1, smul_zero]`. Conclude with `Subtype.ext (sub_eq_zero.1 h2.symm)`. Introduce and unpack `⟨u, hu, j, hj⟩`. Take `⟨a, ha⟩` from `exists_inv (hk.pow_right j)`.

Establish `h1 : M • u = 0`. Rewrite using `[← ha _ (M • u) (by rw [smul_comm, hj, smul_zero]), smul_smul k, hQ' u hu, smul_zero]`. Take `⟨v, rfl⟩` from `honto u h1`. Take `⟨w, hw⟩` from `(hker _).1 ((hev v).symm.trans hu)`. Establish `h2 : M • (G w - k • v) = 0`.

Rewrite using `[smul_sub, smul_smul, mul_comm, ← hGQ, hw, map_nsmul, sub_self]`. Establish `h3 : φ (Submodule.Quotient.mk w) = k • ev v`. Rewrite using `[hφ, sub_eq_zero.1 (tf M _ hM h2), map_nsmul]`. Use `⟨⟨a • k • a • Submodule.Quotient.mk w, j, ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `h4` using `hφk (ℓ ^ j • Submodule.Quotient.mk w) (by rw [map_nsmul, h3, smul_comm, hj, smul_zero])`.

Rewrite using `[smul_comm k a, smul_comm _ a, smul_comm _ a, smul_comm, smul_comm (ℓ ^ j) k, h4, smul_zero, smul_zero]`. Express the relevant statement in the definitionally equal form `φ _ = ev v`. Rewrite using `[map_zsmul, map_nsmul, map_zsmul, h3, ha _ _ hj, ha _ _ hj]`.
-/
theorem card_ker_eq {W U : Type} [AddCommGroup W] [AddCommGroup U] (Q G : W →ₗ[ℤ] W) (Q' : U →+ U) (ev : W →+ U)
    (k M ℓ : ℕ) (hk : Nat.Coprime k ℓ) (hk0 : k ≠ 0) (hM : M ≠ 0) (tf : ∀ (m : ℕ) (w : W), m ≠ 0 → m • w = 0 → w = 0)
    (hev : ∀ w, Q' (ev w) = ev (Q w)) (hGQ : ∀ w, G (Q w) = (k * M) • w) (hQG : ∀ w, Q (G w) = (k * M) • w)
    (hker : ∀ w, ev w = 0 ↔ ∃ b, w = M • b) (honto : ∀ u, M • u = 0 → ∃ w, ev w = u)
    (hQ' : ∀ u, Q' u = 0 → (k * M) • u = 0) :
    Nat.card {u : U // Q' u = 0 ∧ ∃ j : ℕ, ℓ ^ j • u = 0} =
      Nat.card {c : W ⧸ LinearMap.range Q // ∃ j : ℕ, ℓ ^ j • c = 0} := by
  have hM0 : ∀ w, ev (M • w) = 0 := fun w => (hker _).2 ⟨w, rfl⟩
  let φ : (W ⧸ LinearMap.range Q) →ₗ[ℤ] U := (LinearMap.range Q).liftQ (ev.toIntLinearMap ∘ₗ G) (by
    rintro _ ⟨w, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap]
    rw [hGQ, mul_comm, mul_smul, hM0])
  have hφ : ∀ w, φ (Submodule.Quotient.mk w) = ev (G w) := fun w => rfl
  have hφk : ∀ c, φ c = 0 → k • c = 0 := fun c hc => by
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨b, hb⟩ := (hker _).1 ((hφ w).symm.trans hc)
    have h1 : M • (k • w - Q b) = 0 := by
      rw [smul_sub, smul_smul, mul_comm, ← hQG, hb, map_nsmul, sub_self]
    have h2 := sub_eq_zero.1 (tf M _ hM h1)
    change (LinearMap.range Q).mkQ (k • w) = 0
    rw [h2]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨b, rfl⟩
  symm
  refine Nat.card_eq_of_bijective (fun c => ⟨φ c.1, ?_, ?_⟩) ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ c.1
    rw [← hw, hφ, hev, hQG, mul_comm, mul_smul, hM0]
  · obtain ⟨j, hj⟩ := c.2
    exact ⟨j, by rw [← map_nsmul, hj, map_zero]⟩
  · rintro ⟨c, i, hi⟩ ⟨d, j, hj⟩ h
    have h1 : φ (c - d) = 0 := by rw [map_sub]; exact sub_eq_zero.2 (congrArg Subtype.val h)
    obtain ⟨a, ha⟩ := exists_inv (hk.pow_right (i + j))
    have h2 := ha _ (c - d) (by
      rw [smul_sub, pow_add, mul_smul _ _ d, hj, mul_comm, mul_smul, hi, smul_zero, smul_zero, sub_zero])
    rw [hφk _ h1, smul_zero] at h2
    exact Subtype.ext (sub_eq_zero.1 h2.symm)
  · rintro ⟨u, hu, j, hj⟩
    obtain ⟨a, ha⟩ := exists_inv (hk.pow_right j)
    have h1 : M • u = 0 := by
      rw [← ha _ (M • u) (by rw [smul_comm, hj, smul_zero]), smul_smul k, hQ' u hu, smul_zero]
    obtain ⟨v, rfl⟩ := honto u h1
    obtain ⟨w, hw⟩ := (hker _).1 ((hev v).symm.trans hu)
    have h2 : M • (G w - k • v) = 0 := by
      rw [smul_sub, smul_smul, mul_comm, ← hGQ, hw, map_nsmul, sub_self]
    have h3 : φ (Submodule.Quotient.mk w) = k • ev v := by
      rw [hφ, sub_eq_zero.1 (tf M _ hM h2), map_nsmul]
    refine ⟨⟨a • k • a • Submodule.Quotient.mk w, j, ?_⟩, Subtype.ext ?_⟩
    · have h4 := hφk (ℓ ^ j • Submodule.Quotient.mk w) (by rw [map_nsmul, h3, smul_comm, hj, smul_zero])
      rw [smul_comm k a, smul_comm _ a, smul_comm _ a, smul_comm, smul_comm (ℓ ^ j) k, h4, smul_zero, smul_zero]
    · change φ _ = ev v
      rw [map_zsmul, map_nsmul, map_zsmul, h3, ha _ _ hj, ha _ _ hj]

/- English proof (translation)
Set `e : A ≃ₗ[ℤ] B` to `LinearEquiv.ofFinrankEq A B h`. Establish `h0 : LinearMap.det (i ∘ₗ (e.symm : B →ₗ[ℤ] A)) ≠ 0`. Introduce `h0`. Rewrite `h0` using `[LinearMap.det_eq_zero_iff_ker_ne_bot]`. Conclude with `h0 (LinearMap.ker_eq_bot.2 (hi.comp e.symm.injective))`.

Establish `h1 : g ∘ₗ (i ∘ₗ (e.symm : B →ₗ[ℤ] A)) = (i ∘ₗ (e.symm : B →ₗ[ℤ] A)) ∘ₗ ((e : A →ₗ[ℤ] B) ∘ₗ f ∘ₗ (e.symm : B →ₗ[ℤ] A))`. Use extensionality with `x`. Simplify using `using LinearMap.congr_fun hc (e.symm x)`. Establish `h2` using `congrArg LinearMap.det h1`. Rewrite `h2` using `[LinearMap.det_comp, LinearMap.det_comp (i ∘ₗ _), LinearMap.det_conj, mul_comm]`.

Conclude with `mul_left_cancel₀ h0 h2`.
-/
theorem det_eq_of_intertwine {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module.Free ℤ A] [Module.Finite ℤ A]
    [Module.Free ℤ B] [Module.Finite ℤ B] (h : Module.finrank ℤ A = Module.finrank ℤ B) (f : A →ₗ[ℤ] A) (g : B →ₗ[ℤ] B)
    (i : A →ₗ[ℤ] B) (hi : Function.Injective i) (hc : g ∘ₗ i = i ∘ₗ f) : LinearMap.det g = LinearMap.det f := by
  let e : A ≃ₗ[ℤ] B := LinearEquiv.ofFinrankEq A B h
  have h0 : LinearMap.det (i ∘ₗ (e.symm : B →ₗ[ℤ] A)) ≠ 0 := by
    intro h0
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
    exact h0 (LinearMap.ker_eq_bot.2 (hi.comp e.symm.injective))
  have h1 : g ∘ₗ (i ∘ₗ (e.symm : B →ₗ[ℤ] A)) =
      (i ∘ₗ (e.symm : B →ₗ[ℤ] A)) ∘ₗ ((e : A →ₗ[ℤ] B) ∘ₗ f ∘ₗ (e.symm : B →ₗ[ℤ] A)) := by
    ext x
    simpa using LinearMap.congr_fun hc (e.symm x)
  have h2 := congrArg LinearMap.det h1
  rw [LinearMap.det_comp, LinearMap.det_comp (i ∘ₗ _), LinearMap.det_conj, mul_comm] at h2
  exact mul_left_cancel₀ h0 h2

section Mat
variable {O : Type} [CommRing O] {n : ℕ}

def mact (L : Type) [AddCommGroup L] [Module O L] (mu : Matrix (Fin n) (Fin n) O) : (Fin n → L) →ₗ[O] (Fin n → L) where
  toFun u i := ∑ j, mu i j • u j
  map_add' u v := by ext i; simp [Finset.sum_add_distrib]
  map_smul' a u := by ext i; simp [Finset.smul_sum, smul_comm a]

variable {L : Type} [AddCommGroup L] [Module O L]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mact_apply (mu : Matrix (Fin n) (Fin n) O) (u : Fin n → L) (i : Fin n) : mact L mu u i = ∑ j, mu i j • u j := rfl

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [mact_apply, Matrix.mul_apply, Finset.sum_smul, mul_smul, Finset.smul_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem mact_mul (a b : Matrix (Fin n) (Fin n) O) (u : Fin n → L) : mact L a (mact L b u) = mact L (a * b) u := by
  ext i
  simp only [mact_apply, Matrix.mul_apply, Finset.sum_smul, mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [mact_apply, Matrix.smul_apply, Matrix.one_apply, smul_ite, smul_zero, ite_smul, smul_one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Nat.cast_smul_eq_nsmul, smul_assoc, one_smul, Pi.smul_apply]`.
-/
theorem mact_nat (c : ℕ) (u : Fin n → L) : mact L ((c : O) • (1 : Matrix (Fin n) (Fin n) O)) u = c • u := by
  ext i
  simp only [mact_apply, Matrix.smul_apply, Matrix.one_apply, smul_ite, smul_zero, ite_smul, smul_one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Nat.cast_smul_eq_nsmul, smul_assoc, one_smul, Pi.smul_apply]

/- English proof (translation)
Establish `: Module.Finite ℤ L` using `Module.Finite.trans O L`. Take `⟨r, hr⟩ : ∃ r, r = Module.finrank O L` from `⟨_, rfl⟩`. Take `⟨v, hv⟩` from `exists_linearIndependent_of_le_finrank (R := O) (M := L) hr.le`. Rewrite using `[← hr]`. Set `f : (Fin r → Fin n → O) →ₗ[O] (Fin r → Fin n → O)` to `LinearMap.pi fun s => (Matrix.toLin' q).comp (LinearMap.proj s)`.

Establish `hf : LinearMap.det f = q.det ^ r`. Simplify using `[f, LinearMap.det_pi]`. Set `i : (Fin r → Fin n → O) →ₗ[O] (Fin n → L)` to `{ toFun c j := ∑ s, c s j • v s map_add' c d := by ext j; simp [add_smul, Finset.sum_add_distrib] map_smul' a c := by ext j; simp [Finset.smul_sum, mul_smul] }`. Establish `hi : Function.Injective i`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `c hc`. Use extensionality with `s j`. Establish `h1 : ∑ s, c s j • v s = 0` using `congrFun hc j`. Conclude with `Fintype.linearIndependent_iff.1 hv (fun s => c s j) h1 s`. Rewrite using `[det_eq_of_intertwine ?_ (f.restrictScalars ℤ) _ (i.restrictScalars ℤ) hi ?_, LinearMap.det_restrictScalars, hf, map_pow]`.

Simplify using `only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Rewrite using `[finrank_int_eq_mul_of_finite (O := O) (M := L), ← hr]`. Expand and normalize the polynomial expressions, which then agree. Use `LinearMap.ext fun c => funext fun j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `∑ b, q j b • ∑ s, c s b • v s = ∑ s, (q.mulVec (c s) j) • v s`.

Simplify using `only [Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul, mul_smul]`. Conclude with `Finset.sum_comm`.
-/
theorem det_mact [IsDomain O] [CharZero O] [Module.Free ℤ O] [Module.Finite ℤ O] [Module.Finite O L]
    [Module.Free ℤ L] (q : Matrix (Fin n) (Fin n) O) :
    LinearMap.det ((mact L q).restrictScalars ℤ) = Algebra.norm ℤ q.det ^ Module.finrank O L := by
  have : Module.Finite ℤ L := Module.Finite.trans O L
  obtain ⟨r, hr⟩ : ∃ r, r = Module.finrank O L := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := O) (M := L) hr.le
  rw [← hr]
  let f : (Fin r → Fin n → O) →ₗ[O] (Fin r → Fin n → O) :=
    LinearMap.pi fun s => (Matrix.toLin' q).comp (LinearMap.proj s)
  have hf : LinearMap.det f = q.det ^ r := by
    simp [f, LinearMap.det_pi]
  let i : (Fin r → Fin n → O) →ₗ[O] (Fin n → L) :=
    { toFun c j := ∑ s, c s j • v s
      map_add' c d := by ext j; simp [add_smul, Finset.sum_add_distrib]
      map_smul' a c := by ext j; simp [Finset.smul_sum, mul_smul] }
  have hi : Function.Injective i := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    ext s j
    have h1 : ∑ s, c s j • v s = 0 := congrFun hc j
    exact Fintype.linearIndependent_iff.1 hv (fun s => c s j) h1 s
  rw [det_eq_of_intertwine ?_ (f.restrictScalars ℤ) _ (i.restrictScalars ℤ) hi ?_, LinearMap.det_restrictScalars, hf,
    map_pow]
  · simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [finrank_int_eq_mul_of_finite (O := O) (M := L), ← hr]; ring
  · refine LinearMap.ext fun c => funext fun j => ?_
    change ∑ b, q j b • ∑ s, c s b • v s = ∑ s, (q.mulVec (c s) j) • v s
    simp only [Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm

/- English proof (translation)
Establish `: Module.Finite ℤ L` using `Module.Finite.trans O L`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `hℓ.one_lt.ne' (by simpa using hk)`. Establish `hc : k * M ≠ 0` using `mul_ne_zero hk0 hM.ne'`.

Establish `tf : ∀ (m : ℕ) (w : Fin n → L), m ≠ 0 → m • w = 0 → w = 0` using `fun m w hm h => by`. Rewrite `h` using `[← natCast_zsmul]`. Conclude with `(smul_eq_zero.1 h).resolve_left (by exact_mod_cast hm)`. Establish `hGQ : ∀ w, mact L g (mact L q w) = (k * M) • w` using `fun w => by rw [mact_mul, hgq, mact_nat]`. Establish `hdet : q.det ≠ 0`.

Introduce `h`. Establish `h1` using `congrArg Matrix.det hgq`. Rewrite `h1` using `[Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `pow_ne_zero _ (Nat.cast_ne_zero.2 hc) h1.symm`. Establish `hqg : q * g = ((k * M : ℕ) : O) • (1 : Matrix (Fin n) (Fin n) O)`.

Establish `h1 : (q * g - ((k * M : ℕ) : O) • (1 : Matrix (Fin n) (Fin n) O)) * q = 0`. Rewrite using `[sub_mul, Matrix.mul_assoc, hgq]`. Simplify using the standard rewrite rules. Establish `h2` using `congrArg (· * q.adjugate) h1`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.zero_mul] at h2`.

Conclude with `sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hdet)`. Establish `hQG : ∀ w, mact L q (mact L g w) = (k * M) • w` using `fun w => by rw [mact_mul, hqg, mact_nat]`. Establish `hinj : Function.Injective ((mact L q).restrictScalars ℤ)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `w hw`.

Use `tf _ w hc ?_` and prove the remaining obligations. Rewrite using `[← hGQ, show mact L q w = 0 from hw, map_zero]`. Establish `hcard : Nat.card ((Fin n → L) ⧸ LinearMap.range ((mact L q).restrictScalars ℤ)) = (Algebra.norm ℤ q.det).natAbs ^ Module.finrank O L`. Rewrite using `[← Submodule.natAbs_det_equiv _ (LinearEquiv.ofInjective _ hinj), ← Int.natAbs_pow, ← det_mact (L := L) q]`. Use `congr 2`.

Establish `hfin : Finite ((Fin n → L) ⧸ LinearMap.range ((mact L q).restrictScalars ℤ))`. Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Rewrite using `[hcard]`. Conclude with `pow_ne_zero _ (Int.natAbs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 hdet))`. Rewrite using `[← hcard, ← card_primary _ ℓ hℓ]`.

Use `card_ker_eq ((mact L q).restrictScalars ℤ) ((mact L g).restrictScalars ℤ) (mact P q).toAddMonoidHom (ev.compLeft (Fin n)).toAddMonoidHom k M ℓ hk hk0 hM.ne' tf (fun w => ?_) hGQ hQG (fun w => ?_) (fun u hu => ?_) (fun u hu => ?_)` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[mact_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h choose b hb using fun i => (hker (w i)).1 (congrFun h i)`.

Conclude with `⟨b, funext hb⟩`. Introduce and unpack `⟨b, rfl⟩`. Conclude with `funext fun i => (hker _).2 ⟨b i, rfl⟩`. Use `choose a ha using fun i => honto (u i) (congrFun hu i)`. Conclude with `⟨a, funext ha⟩`.

Rewrite using `[← mact_nat (O := O), ← hgq, ← mact_mul, show mact P q u = 0 from hu, map_zero]`.
-/
theorem card_kills [IsDomain O] [CharZero O] [Module.Free ℤ O] [Module.Finite ℤ O] [Module.Finite O L]
    [Module.Free ℤ L] {P : Type} [AddCommGroup P] [Module O P] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (q g : Matrix (Fin n) (Fin n) O) (k M : ℕ) (hk : Nat.Coprime k ℓ) (hM : 0 < M)
    (hgq : g * q = ((k * M : ℕ) : O) • (1 : Matrix (Fin n) (Fin n) O)) (ev : L →ₗ[O] P)
    (hker : ∀ a, ev a = 0 ↔ ∃ b, a = M • b) (honto : ∀ w : P, M • w = 0 → ∃ a, ev a = w) :
    Nat.card {u : Fin n → P // mact P q u = 0 ∧ ∃ j : ℕ, ℓ ^ j • u = 0} =
      ℓ ^ ((Algebra.norm ℤ q.det).natAbs ^ Module.finrank O L).factorization ℓ := by
  have : Module.Finite ℤ L := Module.Finite.trans O L
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hℓ.one_lt.ne' (by simpa using hk)
  have hc : k * M ≠ 0 := mul_ne_zero hk0 hM.ne'
  have tf : ∀ (m : ℕ) (w : Fin n → L), m ≠ 0 → m • w = 0 → w = 0 := fun m w hm h => by
    rw [← natCast_zsmul] at h
    exact (smul_eq_zero.1 h).resolve_left (by exact_mod_cast hm)
  have hGQ : ∀ w, mact L g (mact L q w) = (k * M) • w := fun w => by rw [mact_mul, hgq, mact_nat]
  have hdet : q.det ≠ 0 := by
    intro h
    have h1 := congrArg Matrix.det hgq
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hc) h1.symm
  have hqg : q * g = ((k * M : ℕ) : O) • (1 : Matrix (Fin n) (Fin n) O) := by
    have h1 : (q * g - ((k * M : ℕ) : O) • (1 : Matrix (Fin n) (Fin n) O)) * q = 0 := by
      rw [sub_mul, Matrix.mul_assoc, hgq]; simp
    have h2 := congrArg (· * q.adjugate) h1
    simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.zero_mul] at h2
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hdet)
  have hQG : ∀ w, mact L q (mact L g w) = (k * M) • w := fun w => by rw [mact_mul, hqg, mact_nat]
  have hinj : Function.Injective ((mact L q).restrictScalars ℤ) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    refine tf _ w hc ?_
    rw [← hGQ, show mact L q w = 0 from hw, map_zero]
  have hcard : Nat.card ((Fin n → L) ⧸ LinearMap.range ((mact L q).restrictScalars ℤ)) =
      (Algebra.norm ℤ q.det).natAbs ^ Module.finrank O L := by
    rw [← Submodule.natAbs_det_equiv _ (LinearEquiv.ofInjective _ hinj), ← Int.natAbs_pow, ← det_mact (L := L) q]
    congr 2
  have hfin : Finite ((Fin n → L) ⧸ LinearMap.range ((mact L q).restrictScalars ℤ)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact pow_ne_zero _ (Int.natAbs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 hdet))
  rw [← hcard, ← card_primary _ ℓ hℓ]
  refine card_ker_eq ((mact L q).restrictScalars ℤ) ((mact L g).restrictScalars ℤ) (mact P q).toAddMonoidHom
    (ev.compLeft (Fin n)).toAddMonoidHom k M ℓ hk hk0 hM.ne' tf (fun w => ?_) hGQ hQG (fun w => ?_) (fun u hu => ?_)
    (fun u hu => ?_)
  · ext i
    simp [mact_apply]
  · constructor
    · intro h
      choose b hb using fun i => (hker (w i)).1 (congrFun h i)
      exact ⟨b, funext hb⟩
    · rintro ⟨b, rfl⟩
      exact funext fun i => (hker _).2 ⟨b i, rfl⟩
  · choose a ha using fun i => honto (u i) (congrFun hu i)
    exact ⟨a, funext ha⟩
  · rw [← mact_nat (O := O), ← hgq, ← mact_mul, show mact P q u = 0 from hu, map_zero]
end Mat

end GlobalTheory.TorsCount

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo K _ x ℓ hℓ n q g k M hk hM hgq hall`. Take `⟨ev, hadd, hlin, hker, honto⟩` from `((GlobalTheory.T.torsion_rational_over_finite_extension_level_structure E H Dw l Xo K x M hM).2 hall).2`. Use `letI := ZPart.ptMod Xo (ptO Xo x)`. Use `Dw.fin` as an intermediate fact. Use `datum_free_int Dw` as an intermediate fact.

Set `ev' : Dw.La →ₗ[𝓞 E] Additive (ptO Xo x ⟶ Xo.univ.t.G)` to `{ toFun a := Additive.ofMul (ev a) map_add' a b := congrArg Additive.ofMul (hadd a b) map_smul' o a := congrArg Additive.ofMul (hlin o a) }`. Rewrite using `[← Dw.rank, ← TorsCount.card_kills ℓ hℓ q g k M hk hM hgq ev' (fun a => hker a) (fun w hw => honto w.toMul hw)]`. Use `Nat.card_congr (Equiv.subtypeEquiv (Equiv.piCongrRight fun _ => Additive.ofMul) fun u => ?_)` and prove the remaining obligations. Use `and_congr ((ZPart.kills_iff Xo q u).trans funext_iff.symm) ⟨fun h => ?_, fun ⟨j, hj⟩ b => ⟨j, congrFun hj b⟩⟩` and prove the remaining obligations. Use `choose e he using h`.

Use `⟨∑ b, e b, funext fun b => ?_⟩` and prove the remaining obligations. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le (Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))`. Express the relevant statement in the definitionally equal form `u b ^ (ℓ ^ ∑ b, e b) = 1`. Rewrite using `[hd, pow_add, pow_mul, he, one_pow]`.
-/
theorem card_kills_primary :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (ℓ : ℕ), ℓ.Prime → ∀ (n : ℕ) (q g : Matrix (Fin n) (Fin n) (𝓞 E)) (k M : ℕ), Nat.Coprime k ℓ → 0 < M → g * q = ((k * M : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) → AllRat Xo x M → Nat.card {u : Fin n → (ptO Xo x ⟶ Xo.univ.t.G) // Kills Xo q u ∧ ∀ b, (∃ j : ℕ, u b ^ (ℓ ^ j) = 1)} = ℓ ^ ((Algebra.norm ℤ q.det).natAbs ^ (Dw.p + Dw.q)).factorization ℓ := by
  intro E _ _ _ H Dw l Xo K _ x ℓ hℓ n q g k M hk hM hgq hall
  obtain ⟨ev, hadd, hlin, hker, honto⟩ := ((GlobalTheory.T.torsion_rational_over_finite_extension_level_structure E H Dw l Xo K x M hM).2 hall).2
  letI := ZPart.ptMod Xo (ptO Xo x)
  have := Dw.fin
  have := datum_free_int Dw
  let ev' : Dw.La →ₗ[𝓞 E] Additive (ptO Xo x ⟶ Xo.univ.t.G) :=
    { toFun a := Additive.ofMul (ev a)
      map_add' a b := congrArg Additive.ofMul (hadd a b)
      map_smul' o a := congrArg Additive.ofMul (hlin o a) }
  rw [← Dw.rank, ← TorsCount.card_kills ℓ hℓ q g k M hk hM hgq ev' (fun a => hker a) (fun w hw => honto w.toMul hw)]
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.piCongrRight fun _ => Additive.ofMul) fun u => ?_)
  refine and_congr ((ZPart.kills_iff Xo q u).trans funext_iff.symm) ⟨fun h => ?_, fun ⟨j, hj⟩ b => ⟨j, congrFun hj b⟩⟩
  choose e he using h
  refine ⟨∑ b, e b, funext fun b => ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
  change u b ^ (ℓ ^ ∑ b, e b) = 1
  rw [hd, pow_add, pow_mul, he, one_pow]

end GlobalTheory
