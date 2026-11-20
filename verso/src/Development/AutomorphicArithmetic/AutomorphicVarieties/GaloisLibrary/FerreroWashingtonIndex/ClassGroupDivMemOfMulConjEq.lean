import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

/- English proof (translation)
Use `UniqueFactorizationMonoid.induction_on_prime (P := fun I => I ≠ 0 → ∀ J : M, J ≠ 0 → I * σ I = J * σ J → f I / f J ∈ H) I ?_ ?_ ?_` and prove the remaining obligations. Introduce `h`. Conclude with `absurd rfl h`. Introduce `x hx _ J _ hxJ`. Rewrite `hx` using `[isUnit_iff_eq_one]`.

Substitute `hx` using the available equality. Rewrite `hxJ` using `[map_one, mul_one]`. Establish `hJ1 : J = 1` using `isUnit_iff_eq_one.mp (Units.mkOfMulEqOne J (σ J) hxJ.symm).isUnit`. Substitute `hJ1` using the available equality. Rewrite using `[div_self']`.

Conclude with `H.one_mem`. Introduce `a p ha hp ih _ J hJ hE`. Establish `h0 : σ 0 = 0`. Establish `h` using `map_mul σ 0 (σ.symm 0)`. Rewrite `h` using `[zero_mul, MulEquiv.apply_symm_apply, mul_zero]`. Then use the resulting hypothesis.

Establish `hne : ∀ x : M, x ≠ 0 → σ x ≠ 0`. Introduce `x hx h`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← hσ x, h, h0]`. Establish `hp0 : p ≠ 0` using `hp.ne_zero`.

Establish `hsp0` using `hne p hp0`. Establish `hd : p ∣ J * σ J` using `hE ▸ dvd_mul_of_dvd_left (dvd_mul_right p a) _`. Rewrite `hE` using `[map_mul]`. Break down `hp.dvd_or_dvd hd with ⟨J₀, rfl⟩ | ⟨K₀, hK⟩` into its components or cases. Establish `hJ0 : J₀ ≠ 0` using `right_ne_zero_of_mul hJ`.

Rewrite `hE` using `[map_mul]`. Establish `e1 : (p * σ p) * (a * σ a) = (p * σ p) * (J₀ * σ J₀)`. Simplify `hE` using `only [mul_comm, mul_assoc, mul_left_comm]`. Establish `e2` using `mul_left_cancel₀ (mul_ne_zero hp0 hsp0) e1`. Rewrite using `[hf p a hp0 ha, hf p J₀ hp0 hJ0, mul_div_mul_left_eq_div]`.

Conclude with `ih ha J₀ hJ0 e2`. Establish `hsJ` using `hne J hJ`. Establish `hK0 : K₀ ≠ 0`. Rewrite `hsJ` using `[hK]`. Conclude with `right_ne_zero_of_mul hsJ`.

Establish `hsK0` using `hne K₀ hK0`. Establish `hJ' : J = σ p * σ K₀` using `by rw [← hσ J, hK, map_mul]`. Rewrite `hE` using `[hK, hJ']`. Establish `e1 : (p * σ p) * (a * σ a) = (p * σ p) * (K₀ * σ K₀)`. Simplify `hE` using `only [mul_comm, mul_assoc, mul_left_comm]`.

Establish `e2` using `mul_left_cancel₀ (mul_ne_zero hp0 hsp0) e1`. Establish `key` using `H.mul_mem (hH p hp0) (H.mul_mem (ih ha K₀ hK0 e2) (hH K₀ hK0))`. Rewrite `key` using `[div_mul_div_cancel, div_mul_div_comm]`. Rewrite using `[hJ', hf p a hp0 ha, hf (σ p) (σ K₀) hsp0 hsK0]`. Conclude with `key`.
-/
private theorem quotient_mem_of_norm_eq_involution {M C : Type} [CommMonoidWithZero M] [UniqueFactorizationMonoid M] [Subsingleton Mˣ]
    [CommGroup C] (σ : M ≃* M) (hσ : ∀ x, σ (σ x) = x) (H : Subgroup C) (f : M → C)
    (hf : ∀ a b, a ≠ 0 → b ≠ 0 → f (a * b) = f a * f b) (hH : ∀ a, a ≠ 0 → f a / f (σ a) ∈ H) (I : M) :
    I ≠ 0 → ∀ J : M, J ≠ 0 → I * σ I = J * σ J → f I / f J ∈ H := by
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun I => I ≠ 0 → ∀ J : M, J ≠ 0 → I * σ I = J * σ J → f I / f J ∈ H) I ?_ ?_ ?_
  · intro h
    exact absurd rfl h
  · intro x hx _ J _ hxJ
    rw [isUnit_iff_eq_one] at hx
    subst hx
    rw [map_one, mul_one] at hxJ
    have hJ1 : J = 1 := isUnit_iff_eq_one.mp (Units.mkOfMulEqOne J (σ J) hxJ.symm).isUnit
    subst hJ1
    rw [div_self']
    exact H.one_mem
  · intro a p ha hp ih _ J hJ hE
    have h0 : σ 0 = 0 := by
      have h := map_mul σ 0 (σ.symm 0)
      rwa [zero_mul, MulEquiv.apply_symm_apply, mul_zero] at h
    have hne : ∀ x : M, x ≠ 0 → σ x ≠ 0 := by
      intro x hx h
      apply hx
      rw [← hσ x, h, h0]
    have hp0 : p ≠ 0 := hp.ne_zero
    have hsp0 := hne p hp0
    have hd : p ∣ J * σ J := hE ▸ dvd_mul_of_dvd_left (dvd_mul_right p a) _
    rw [map_mul] at hE
    rcases hp.dvd_or_dvd hd with ⟨J₀, rfl⟩ | ⟨K₀, hK⟩
    · have hJ0 : J₀ ≠ 0 := right_ne_zero_of_mul hJ
      rw [map_mul] at hE
      have e1 : (p * σ p) * (a * σ a) = (p * σ p) * (J₀ * σ J₀) := by
        simpa only [mul_comm, mul_assoc, mul_left_comm] using hE
      have e2 := mul_left_cancel₀ (mul_ne_zero hp0 hsp0) e1
      rw [hf p a hp0 ha, hf p J₀ hp0 hJ0, mul_div_mul_left_eq_div]
      exact ih ha J₀ hJ0 e2
    · have hsJ := hne J hJ
      have hK0 : K₀ ≠ 0 := by
        rw [hK] at hsJ
        exact right_ne_zero_of_mul hsJ
      have hsK0 := hne K₀ hK0
      have hJ' : J = σ p * σ K₀ := by rw [← hσ J, hK, map_mul]
      rw [hK, hJ'] at hE
      have e1 : (p * σ p) * (a * σ a) = (p * σ p) * (K₀ * σ K₀) := by
        simpa only [mul_comm, mul_assoc, mul_left_comm] using hE
      have e2 := mul_left_cancel₀ (mul_ne_zero hp0 hsp0) e1
      have key := H.mul_mem (hH p hp0) (H.mul_mem (ih ha K₀ hK0 e2) (hH K₀ hK0))
      rw [div_mul_div_cancel, div_mul_div_comm] at key
      rw [hJ', hf p a hp0 ha, hf (σ p) (σ K₀) hsp0 hsK0]
      exact key

/- English proof (translation)
Introduce `K _ _ τ I J hτ hIJ`. Establish `hee : ∀ x : 𝓞 K, RingOfIntegers.mapRingEquiv τ (RingOfIntegers.mapRingEquiv τ x) = x` using `fun x => RingOfIntegers.ext (hτ x)`. Establish `hmap : ∀ I : Ideal (𝓞 K), Ideal.map (RingOfIntegers.mapRingEquiv τ) (Ideal.map (RingOfIntegers.mapRingEquiv τ) I) = I`. Introduce `I`. Use `show Ideal.map (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K) (Ideal.map (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K) I) = I`.

Rewrite using `[Ideal.map_map]`. Use `Ideal.map_id I` and compare the differences between its conclusion and the goal. Conclude with `RingHom.ext fun x => hee x`. Set `σ : Ideal (𝓞 K) ≃* Ideal (𝓞 K)` to `{ toFun := Ideal.map (RingOfIntegers.mapRingEquiv τ) invFun := Ideal.map (RingOfIntegers.mapRingEquiv τ) left_inv := hmap right_inv := hmap map_mul' := Ideal.map_mul (RingOfIntegers.mapRingEquiv τ) }`. Set `f : Ideal (𝓞 K) → ClassGroup (𝓞 K)` to `fun a => if h : a ∈ (Ideal (𝓞 K))⁰ then ClassGroup.mk0 ⟨a, h⟩ else 1`.

Establish `hfv : ∀ a (h : a ∈ (Ideal (𝓞 K))⁰), f a = ClassGroup.mk0 ⟨a, h⟩` using `fun a h => dif_pos h`. Establish `hf : ∀ a b, a ≠ 0 → b ≠ 0 → f (a * b) = f a * f b`. Introduce `a b ha hb`. Establish `ha'` using `mem_nonZeroDivisors_of_ne_zero ha`. Establish `hb'` using `mem_nonZeroDivisors_of_ne_zero hb`.

Rewrite using `[hfv a ha', hfv b hb', hfv (a * b) (Submonoid.mul_mem _ ha' hb'), ← map_mul]`. Both sides reduce to the same expression. Establish `hH : ∀ a, a ≠ 0 → f a / f (σ a) ∈ difR (clMap τ)`. Introduce `a ha`. Establish `ha'` using `mem_nonZeroDivisors_of_ne_zero ha`.

Establish `hs' : σ a ∈ (Ideal (𝓞 K))⁰` using `(idMap τ ⟨a, ha'⟩).2`. Rewrite using `[hfv a ha', hfv _ hs']`. Use `⟨ClassGroup.mk0 ⟨a, ha'⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.div_apply, MonoidHom.id_apply, class_map_mk0]`. Both sides reduce to the same expression.

Establish `key` using `quotient_mem_of_norm_eq_involution σ (fun x => hmap x) (difR (clMap τ)) f hf hH (I : Ideal (𝓞 K)) (nonZeroDivisors.coe_ne_zero I) J (nonZeroDivisors.coe_ne_zero J) (congrArg Subtype.val hIJ)`. Rewrite `key` using `[hfv _ I.2, hfv _ J.2]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.FW.classGroup_div_mem_of_mul_conj_eq :
    ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K) (I J : (Ideal (𝓞 K))⁰), (∀ x, τ (τ x) = x) → I * idMap τ I = J * idMap τ J → ClassGroup.mk0 I / ClassGroup.mk0 J ∈ difR (clMap τ) := by
  intro K _ _ τ I J hτ hIJ
  classical
  have hee : ∀ x : 𝓞 K, RingOfIntegers.mapRingEquiv τ (RingOfIntegers.mapRingEquiv τ x) = x :=
    fun x => RingOfIntegers.ext (hτ x)
  have hmap : ∀ I : Ideal (𝓞 K), Ideal.map (RingOfIntegers.mapRingEquiv τ)
      (Ideal.map (RingOfIntegers.mapRingEquiv τ) I) = I := by
    intro I
    show Ideal.map (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
      (Ideal.map (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K) I) = I
    rw [Ideal.map_map]
    convert Ideal.map_id I
    exact RingHom.ext fun x => hee x
  let σ : Ideal (𝓞 K) ≃* Ideal (𝓞 K) :=
    { toFun := Ideal.map (RingOfIntegers.mapRingEquiv τ)
      invFun := Ideal.map (RingOfIntegers.mapRingEquiv τ)
      left_inv := hmap
      right_inv := hmap
      map_mul' := Ideal.map_mul (RingOfIntegers.mapRingEquiv τ) }
  let f : Ideal (𝓞 K) → ClassGroup (𝓞 K) := fun a =>
    if h : a ∈ (Ideal (𝓞 K))⁰ then ClassGroup.mk0 ⟨a, h⟩ else 1
  have hfv : ∀ a (h : a ∈ (Ideal (𝓞 K))⁰), f a = ClassGroup.mk0 ⟨a, h⟩ := fun a h => dif_pos h
  have hf : ∀ a b, a ≠ 0 → b ≠ 0 → f (a * b) = f a * f b := by
    intro a b ha hb
    have ha' := mem_nonZeroDivisors_of_ne_zero ha
    have hb' := mem_nonZeroDivisors_of_ne_zero hb
    rw [hfv a ha', hfv b hb', hfv (a * b) (Submonoid.mul_mem _ ha' hb'), ← map_mul]
    rfl
  have hH : ∀ a, a ≠ 0 → f a / f (σ a) ∈ difR (clMap τ) := by
    intro a ha
    have ha' := mem_nonZeroDivisors_of_ne_zero ha
    have hs' : σ a ∈ (Ideal (𝓞 K))⁰ := (idMap τ ⟨a, ha'⟩).2
    rw [hfv a ha', hfv _ hs']
    refine ⟨ClassGroup.mk0 ⟨a, ha'⟩, ?_⟩
    rw [MonoidHom.div_apply, MonoidHom.id_apply, class_map_mk0]
    rfl
  have key := quotient_mem_of_norm_eq_involution σ (fun x => hmap x) (difR (clMap τ)) f hf hH (I : Ideal (𝓞 K))
    (nonZeroDivisors.coe_ne_zero I) J (nonZeroDivisors.coe_ne_zero J) (congrArg Subtype.val hIJ)
  rwa [hfv _ I.2, hfv _ J.2] at key
