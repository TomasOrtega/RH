import Mathlib
open IsLocalRing

namespace GlobalTheory.CoordsAlg

noncomputable def cotFun {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A)
    (f : I →ₗ[R] R) (hf : ∀ x : I, (x : A) ∈ I ^ 2 → f x = 0) : Module.Dual R I.Cotangent :=
  ((I • ⊤ : Submodule A I).restrictScalars R).liftQ f (fun x hx => by
      refine LinearMap.mem_ker.mpr (hf x ?_)
      rw [← Ideal.toCotangent_eq_zero]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hx) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R (I • ⊤ : Submodule A I)).symm.toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cotFun_toCotangent {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A)
    (f : I →ₗ[R] R) (hf : ∀ x : I, (x : A) ∈ I ^ 2 → f x = 0) (x : I) :
    cotFun I f hf (I.toCotangent x) = f x := rfl

/- English proof (translation)
Introduce `R A _ _ _ _ _ _ e he hfree hfin n dv hadd hmul halg huniq`. Use `set I := RingHom.ker e with hIdef`. Set `dH : Fin n → A →+ R` to `fun a => AddMonoidHom.mk' (dv a) (hadd a)`. Establish `hdH : ∀ a x, dv a x = dH a x` using `fun _ _ => rfl`. Establish `hsmul : ∀ a r x, dv a (algebraMap R A r * x) = r * dv a x`.

Introduce `a r x`. Rewrite using `[hmul, he, halg]`. Expand and normalize the polynomial expressions, which then agree. Establish `hI2 : ∀ a x, x ∈ I ^ 2 → dv a x = 0`. Introduce `a x hx`.

Rewrite `hx` using `[pow_two]`. Use `Submodule.mul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `u hu v hv`. Rewrite using `[hmul, (RingHom.mem_ker).1 hu, (RingHom.mem_ker).1 hv]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `u v hu hv`. Rewrite using `[hadd, hu, hv, add_zero]`. Establish `hdec : ∀ x : A, x - algebraMap R A (e x) ∈ I` using `fun x => by`. Simplify using `[I, RingHom.mem_ker, he]`. Set `fa : Fin n → (I →ₗ[R] R)` to `fun a => { toFun := fun x => dv a x map_add' := fun x y => hadd a x y map_smul' := fun r x => by`.

Simplify using `only [Submodule.coe_smul_of_tower, Algebra.smul_def, RingHom.id_apply, smul_eq_mul]`. Conclude with `hsmul a r x }`. Set `ℓ : Fin n → Module.Dual R I.Cotangent` to `fun a => cotFun I (fa a) (fun x hx => hI2 a x hx)`. Establish `hℓ : ∀ a (x : I), ℓ a (I.toCotangent x) = dv a x` using `fun _ _ => rfl`. Set `Ψ : (Fin n → R) →ₗ[R] Module.Dual R I.Cotangent` to `∑ a, (LinearMap.proj a : (Fin n → R) →ₗ[R] R).smulRight (ℓ a)`.

Establish `hΨ : ∀ c (x : I), Ψ c (I.toCotangent x) = ∑ a, c a * dv a x`. Introduce `c x`. Simplify using `[Ψ, LinearMap.sum_apply, hℓ]`. Establish `hΨinj : Function.Injective Ψ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `c hc`. Establish `h0 : ∀ x : A, ∑ a, c a * dv a x = 0`. Introduce `x`. Establish `hx` using `hΨ c ⟨_, hdec x⟩`. Rewrite `hx` using `[hc]`.

Establish `: ∀ a, dv a (x - algebraMap R A (e x)) = dv a x`. Introduce `a`. Rewrite using `[hdH, map_sub, ← hdH, ← hdH, halg, sub_zero]`. Simplify using `only [this] at hx`. Conclude with `hx.symm`.

Take `⟨c0, -, hc0⟩` from `huniq (fun _ => 0) (fun _ _ => by simp) (fun _ _ => by simp) (fun _ => rfl)`. Establish `h1 : c = c0` using `hc0 c (fun x => (h0 x).symm)`. Establish `h2 : (0 : Fin n → R) = c0` using `hc0 0 (fun x => by simp)`. Rewrite using `[h1, ← h2]`. Establish `hΨsurj : Function.Surjective Ψ`.

Introduce `φ`. Set `D : A → R` to `fun x => φ (I.toCotangent ⟨_, hdec x⟩)`. Establish `Dadd : ∀ x y, D (x + y) = D x + D y`. Introduce `x y`. Simplify using `only [D, ← map_add]`.

Use `congr 2`. Use `ext`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `Dalg : ∀ r, D (algebraMap R A r) = 0`.

Introduce `r`. Simplify using `only [D]`. Establish `: (⟨_, hdec (algebraMap R A r)⟩ : I) = 0` using `by ext; simp [he]`. Rewrite using `[this, map_zero, map_zero]`. Establish `Dmul : ∀ x y, D (x * y) = e x * D y + e y * D x`.

Introduce `x y`. Establish `hsq : (x - algebraMap R A (e x)) * (y - algebraMap R A (e y)) ∈ I ^ 2`. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul (hdec x) (hdec y)`. Establish `key : (⟨_, hdec (x * y)⟩ : I) = e x • (⟨_, hdec y⟩ : I) + e y • (⟨_, hdec x⟩ : I) + ⟨_, Ideal.pow_le_self two_ne_zero hsq⟩`.

Use `ext`. Simplify using `only [Submodule.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hw0 : I.toCotangent ⟨(x - algebraMap R A (e x)) * (y - algebraMap R A (e y)), Ideal.pow_le_self two_ne_zero hsq⟩ = 0` using `(I.toCotangent_eq_zero _).2 hsq`. Simplify using `only [D]`.

Rewrite using `[key]`. Simplify using `only [map_add, LinearMap.map_smul_of_tower, hw0, map_zero, add_zero, map_smul, smul_eq_mul]`. Take `⟨c, hc, -⟩` from `huniq D Dadd Dmul Dalg`. Use `⟨c, ?_⟩` and prove the remaining obligations. Use extensionality with `w`.

Take `⟨x, rfl⟩` from `I.toCotangent_surjective w`. Rewrite using `[hΨ, ← hc]`. Simplify using `only [D]`. Use `congr 2`. Use `ext`.

Simplify using `[(RingHom.mem_ker).1 x.2]`. Set `Ψe : (Fin n → R) ≃ₗ[R] Module.Dual R I.Cotangent` to `LinearEquiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩`. Establish `hΨsingle : ∀ a, Ψ (Pi.single a 1) = ℓ a`. Introduce `a`. Use extensionality with `w`.

Take `⟨x, rfl⟩` from `I.toCotangent_surjective w`. Rewrite using `[hΨ, hℓ]`. Simplify using `[Pi.single_apply]`. Set `w : Fin n → I.Cotangent` to `fun i => (Module.evalEquiv R I.Cotangent).symm ((LinearMap.proj i : (Fin n → R) →ₗ[R] R) ∘ₗ Ψe.symm.toLinearMap)`. Establish `hw : ∀ a i, ℓ a (w i) = if a = i then 1 else 0`.

Introduce `a i`. Simplify using `only [w, Module.apply_evalEquiv_symm_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply]`. Establish `: Ψe.symm (ℓ a) = Pi.single a 1`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Conclude with `(hΨsingle a).symm`.

Rewrite using `[this]`. Distinguish the cases in `h : a = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Pi.single_apply, Ne.symm h]`.

Use `choose y hy using fun i => I.toCotangent_surjective (w i)`. Establish `hzI : ∀ i, (y i : A) ∈ I` using `fun i => (y i).2`. Establish `hdz : ∀ a i, dv a (y i : A) = if a = i then 1 else 0`. Introduce `a i`. Rewrite using `[← hℓ, hy, hw]`.

Establish `hImax : I ≤ maximalIdeal A`. Introduce `x hx`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Use `hu.map e` as an intermediate fact.

Rewrite `this` using `[(RingHom.mem_ker).1 hx]`. Conclude with `not_isUnit_zero this`. Establish `hnak : I ≤ Ideal.span (Set.range fun i => (y i : A))`. Use `Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A) (IsNoetherian.noetherian I) ?_ ?_` and prove the remaining obligations. Rewrite using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]`.

Introduce `x hx set s := ∑ a, algebraMap R A (dv a x) * (y a : A) with hs`. Establish `hsI : s ∈ Ideal.span (Set.range fun i => (y i : A))` using `Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a, rfl⟩)`. Establish `hsI' : s ∈ I` using `Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hzI a)`. Establish `hr : x - s ∈ I` using `I.sub_mem hx hsI'`. Establish `hdr : ∀ b, dv b (x - s) = 0`.

Introduce `b`. Rewrite using `[hdH, map_sub, hs, map_sum]`. Simplify using `only [← hdH, hsmul, hdz]`. Simplify using the standard rewrite rules. Establish `hcot : I.toCotangent ⟨x - s, hr⟩ = 0`.

Use `(Module.forall_dual_apply_eq_zero_iff R _).1 fun φ => ?_` and prove the remaining obligations. Take `⟨c, rfl⟩` from `hΨsurj φ`. Rewrite using `[hΨ]`. Simplify using `[hdr]`. Establish `hsq : x - s ∈ I ^ 2` using `(I.toCotangent_eq_zero _).1 hcot`.

Establish `hxs : x = s + (x - s)` using `by ring`. Rewrite using `[hxs]`. Use `Submodule.add_mem_sup hsI ?_` and prove the remaining obligations. Rewrite `hsq` using `[pow_two]`. Conclude with `Submodule.smul_mono_left hImax hsq`.

Use `⟨fun i => (y i : A), fun i => (RingHom.mem_ker).1 (y i).2, hdz, ?_⟩` and prove the remaining obligations. Establish `hmapR : (maximalIdeal R).map (algebraMap R A) ≤ maximalIdeal A`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `r hr`. Rewrite using `[Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]`.

Introduce `hu`. Use `hu.map e` as an intermediate fact. Rewrite `this` using `[he]`. Conclude with `(mem_maximalIdeal r).1 hr this`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `x hx`. Establish `hex : e x ∈ maximalIdeal R`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Establish `h1 : algebraMap R A (e x) ∈ maximalIdeal A`.

Use `(maximalIdeal A).sub_mem hx (hImax (hdec x))` as an intermediate fact. Simplify using `using this`. Conclude with `(mem_maximalIdeal _).1 h1 (hu.map _)`. Establish `hxe : x = algebraMap R A (e x) + (x - algebraMap R A (e x))` using `by ring`. Rewrite using `[hxe]`.

Conclude with `Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hex) (hnak (hdec x))`. Use `sup_le hmapR ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hImax (hzI i)`.
-/
theorem coords_of_derivation_basis : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra R A] (e : A →+* R), (∀ r, e (algebraMap R A r) = r) → Module.Free R (RingHom.ker e).Cotangent → Module.Finite R (RingHom.ker e).Cotangent → ∀ (n : ℕ) (dv : Fin n → A → R), (∀ a x y, dv a (x + y) = dv a x + dv a y) → (∀ a x y, dv a (x * y) = e x * dv a y + e y * dv a x) → (∀ a r, dv a (algebraMap R A r) = 0) → (∀ D : A → R, (∀ x y, D (x + y) = D x + D y) → (∀ x y, D (x * y) = e x * D y + e y * D x) → (∀ r, D (algebraMap R A r) = 0) → ∃! c : Fin n → R, ∀ x, D x = ∑ a, c a * dv a x) → ∃ z : Fin n → A, (∀ i, e (z i) = 0) ∧ (∀ a i, dv a (z i) = if a = i then 1 else 0) ∧ maximalIdeal A = (maximalIdeal R).map (algebraMap R A) ⊔ Ideal.span (Set.range z) := by
  intro R A _ _ _ _ _ _ e he hfree hfin n dv hadd hmul halg huniq
  set I := RingHom.ker e with hIdef
  let dH : Fin n → A →+ R := fun a => AddMonoidHom.mk' (dv a) (hadd a)
  have hdH : ∀ a x, dv a x = dH a x := fun _ _ => rfl
  have hsmul : ∀ a r x, dv a (algebraMap R A r * x) = r * dv a x := by
    intro a r x; rw [hmul, he, halg]; ring
  have hI2 : ∀ a x, x ∈ I ^ 2 → dv a x = 0 := by
    intro a x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro u hu v hv
      rw [hmul, (RingHom.mem_ker).1 hu, (RingHom.mem_ker).1 hv]; ring
    · intro u v hu hv; rw [hadd, hu, hv, add_zero]
  have hdec : ∀ x : A, x - algebraMap R A (e x) ∈ I := fun x => by
    simp [I, RingHom.mem_ker, he]
  let fa : Fin n → (I →ₗ[R] R) := fun a =>
    { toFun := fun x => dv a x
      map_add' := fun x y => hadd a x y
      map_smul' := fun r x => by
        simp only [Submodule.coe_smul_of_tower, Algebra.smul_def, RingHom.id_apply, smul_eq_mul]
        exact hsmul a r x }
  let ℓ : Fin n → Module.Dual R I.Cotangent := fun a => cotFun I (fa a) (fun x hx => hI2 a x hx)
  have hℓ : ∀ a (x : I), ℓ a (I.toCotangent x) = dv a x := fun _ _ => rfl
  let Ψ : (Fin n → R) →ₗ[R] Module.Dual R I.Cotangent :=
    ∑ a, (LinearMap.proj a : (Fin n → R) →ₗ[R] R).smulRight (ℓ a)
  have hΨ : ∀ c (x : I), Ψ c (I.toCotangent x) = ∑ a, c a * dv a x := by
    intro c x
    simp [Ψ, LinearMap.sum_apply, hℓ]

  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h0 : ∀ x : A, ∑ a, c a * dv a x = 0 := by
      intro x
      have hx := hΨ c ⟨_, hdec x⟩
      rw [hc] at hx
      have : ∀ a, dv a (x - algebraMap R A (e x)) = dv a x := by
        intro a; rw [hdH, map_sub, ← hdH, ← hdH, halg, sub_zero]
      simp only [this] at hx
      exact hx.symm
    obtain ⟨c0, -, hc0⟩ := huniq (fun _ => 0) (fun _ _ => by simp) (fun _ _ => by simp)
      (fun _ => rfl)
    have h1 : c = c0 := hc0 c (fun x => (h0 x).symm)
    have h2 : (0 : Fin n → R) = c0 := hc0 0 (fun x => by simp)
    rw [h1, ← h2]
  have hΨsurj : Function.Surjective Ψ := by
    intro φ
    let D : A → R := fun x => φ (I.toCotangent ⟨_, hdec x⟩)
    have Dadd : ∀ x y, D (x + y) = D x + D y := by
      intro x y
      simp only [D, ← map_add]
      congr 2
      ext; simp; ring
    have Dalg : ∀ r, D (algebraMap R A r) = 0 := by
      intro r
      simp only [D]
      have : (⟨_, hdec (algebraMap R A r)⟩ : I) = 0 := by ext; simp [he]
      rw [this, map_zero, map_zero]
    have Dmul : ∀ x y, D (x * y) = e x * D y + e y * D x := by
      intro x y
      have hsq : (x - algebraMap R A (e x)) * (y - algebraMap R A (e y)) ∈ I ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul (hdec x) (hdec y)
      have key : (⟨_, hdec (x * y)⟩ : I) = e x • (⟨_, hdec y⟩ : I) + e y • (⟨_, hdec x⟩ : I) +
          ⟨_, Ideal.pow_le_self two_ne_zero hsq⟩ := by
        ext
        simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def, map_mul]
        ring
      have hw0 : I.toCotangent ⟨(x - algebraMap R A (e x)) * (y - algebraMap R A (e y)),
          Ideal.pow_le_self two_ne_zero hsq⟩ = 0 := (I.toCotangent_eq_zero _).2 hsq
      simp only [D]
      rw [key]
      simp only [map_add, LinearMap.map_smul_of_tower, hw0,
        map_zero, add_zero, map_smul, smul_eq_mul]
    obtain ⟨c, hc, -⟩ := huniq D Dadd Dmul Dalg
    refine ⟨c, ?_⟩
    ext w
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective w
    rw [hΨ, ← hc]
    simp only [D]
    congr 2
    ext
    simp [(RingHom.mem_ker).1 x.2]
  let Ψe : (Fin n → R) ≃ₗ[R] Module.Dual R I.Cotangent :=
    LinearEquiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩
  have hΨsingle : ∀ a, Ψ (Pi.single a 1) = ℓ a := by
    intro a
    ext w
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective w
    rw [hΨ, hℓ]
    simp [Pi.single_apply]
  let w : Fin n → I.Cotangent := fun i =>
    (Module.evalEquiv R I.Cotangent).symm
      ((LinearMap.proj i : (Fin n → R) →ₗ[R] R) ∘ₗ Ψe.symm.toLinearMap)
  have hw : ∀ a i, ℓ a (w i) = if a = i then 1 else 0 := by
    intro a i
    simp only [w, Module.apply_evalEquiv_symm_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.proj_apply]
    have : Ψe.symm (ℓ a) = Pi.single a 1 := by
      rw [LinearEquiv.symm_apply_eq]; exact (hΨsingle a).symm
    rw [this]
    by_cases h : a = i
    · subst h; simp
    · simp [h, Pi.single_apply, Ne.symm h]
  choose y hy using fun i => I.toCotangent_surjective (w i)
  have hzI : ∀ i, (y i : A) ∈ I := fun i => (y i).2
  have hdz : ∀ a i, dv a (y i : A) = if a = i then 1 else 0 := by
    intro a i; rw [← hℓ, hy, hw]
  have hImax : I ≤ maximalIdeal A := by
    intro x hx
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map e
    rw [(RingHom.mem_ker).1 hx] at this
    exact not_isUnit_zero this
  have hnak : I ≤ Ideal.span (Set.range fun i => (y i : A)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A)
      (IsNoetherian.noetherian I) ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · intro x hx
      set s := ∑ a, algebraMap R A (dv a x) * (y a : A) with hs
      have hsI : s ∈ Ideal.span (Set.range fun i => (y i : A)) :=
        Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a, rfl⟩)
      have hsI' : s ∈ I := Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hzI a)
      have hr : x - s ∈ I := I.sub_mem hx hsI'
      have hdr : ∀ b, dv b (x - s) = 0 := by
        intro b
        rw [hdH, map_sub, hs, map_sum]
        simp only [← hdH, hsmul, hdz]
        simp
      have hcot : I.toCotangent ⟨x - s, hr⟩ = 0 := by
        refine (Module.forall_dual_apply_eq_zero_iff R _).1 fun φ => ?_
        obtain ⟨c, rfl⟩ := hΨsurj φ
        rw [hΨ]; simp [hdr]
      have hsq : x - s ∈ I ^ 2 := (I.toCotangent_eq_zero _).1 hcot
      have hxs : x = s + (x - s) := by ring
      rw [hxs]
      refine Submodule.add_mem_sup hsI ?_
      rw [pow_two] at hsq
      exact Submodule.smul_mono_left hImax hsq
  refine ⟨fun i => (y i : A), fun i => (RingHom.mem_ker).1 (y i).2, hdz, ?_⟩
  have hmapR : (maximalIdeal R).map (algebraMap R A) ≤ maximalIdeal A := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map e
    rw [he] at this
    exact (mem_maximalIdeal r).1 hr this
  apply le_antisymm
  · intro x hx
    have hex : e x ∈ maximalIdeal R := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h1 : algebraMap R A (e x) ∈ maximalIdeal A := by
        have := (maximalIdeal A).sub_mem hx (hImax (hdec x))
        simpa using this
      exact (mem_maximalIdeal _).1 h1 (hu.map _)
    have hxe : x = algebraMap R A (e x) + (x - algebraMap R A (e x)) := by ring
    rw [hxe]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hex) (hnak (hdec x))
  · refine sup_le hmapR ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hImax (hzI i)

end GlobalTheory.CoordsAlg
