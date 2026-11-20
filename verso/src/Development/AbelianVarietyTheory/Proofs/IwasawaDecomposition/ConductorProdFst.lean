import Mathlib
open IsLocalRing Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `c hc`. Set `g : S →+* FractionRing R × FractionRing S'` to `(RingHom.prodMap (algebraMap R (FractionRing R)) (algebraMap S' (FractionRing S'))).comp e.toRingHom`. Establish `hgx : ∀ x : S, g x = (algebraMap R (FractionRing R) (e x).1, algebraMap S' (FractionRing S') (e x).2)` using `fun x => rfl`. Establish `hg : ∀ y : nonZeroDivisors S, IsUnit (g y)`. Introduce `y`.

Rewrite using `[hgx, Prod.isUnit_iff]`. Establish `h1 : (e y).1 ∈ nonZeroDivisors R`. Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `z hz`. Establish `h0 : e.symm (z, 0) * (y : S) = 0`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, RingEquiv.apply_symm_apply, map_zero]`. Apply the tactic sequence `ext <;> simp [hz]`. Use `(mul_right_mem_nonZeroDivisors_eq_zero_iff y.2).mp h0` as an intermediate fact. Use `congrArg (fun w => (e w).1) this` as an intermediate fact.

Simplify using `using this`. Establish `h2 : (e y).2 ∈ nonZeroDivisors S'`. Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `z hz`. Establish `h0 : e.symm (0, z) * (y : S) = 0`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, RingEquiv.apply_symm_apply, map_zero]`. Apply the tactic sequence `ext <;> simp [hz]`. Use `(mul_right_mem_nonZeroDivisors_eq_zero_iff y.2).mp h0` as an intermediate fact. Use `congrArg (fun w => (e w).2) this` as an intermediate fact.

Simplify using `using this`. Conclude with `⟨IsLocalization.map_units (FractionRing R) (⟨_, h1⟩ : nonZeroDivisors R), IsLocalization.map_units (FractionRing S') (⟨_, h2⟩ : nonZeroDivisors S')⟩`. Set `Θ : FractionRing S →+* FractionRing R × FractionRing S'` to `IsLocalization.lift hg`. Establish `hΘ : ∀ x : S, Θ (algebraMap S (FractionRing S) x) = g x` using `fun x => IsLocalization.lift_eq hg x`. Establish `hΘinj : Function.Injective Θ`.

Rewrite using `[IsLocalization.lift_injective_iff]`. Introduce `x y`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[(IsFractionRing.injective S (FractionRing S)) h]`.

Introduce `h`. Establish `h' : e x = e y`. Rewrite `h` using `[hgx, hgx]`. Use `ext`. Conclude with `IsFractionRing.injective R (FractionRing R) (congrArg Prod.fst h)`.

Conclude with `IsFractionRing.injective S' (FractionRing S') (congrArg Prod.snd h)`. Rewrite using `[e.injective h']`. Take `⟨⟨a, b⟩, rfl⟩` from `IsLocalization.mk'_surjective (nonZeroDivisors R) c`. Establish `hb' : e.symm ((b : R), (1 : S')) ∈ nonZeroDivisors S`. Rewrite using `[mem_nonZeroDivisors_iff_right]`.

Introduce `z hz`. Establish `hz'` using `congrArg e hz`. Rewrite `hz'` using `[map_mul, RingEquiv.apply_symm_apply, map_zero]`. Establish `h1 : (e z).1 * b = 0` using `congrArg Prod.fst hz'`. Establish `h2 : (e z).2 * 1 = 0` using `congrArg Prod.snd hz'`.

Rewrite `h1` using `[mul_right_mem_nonZeroDivisors_eq_zero_iff b.2]`. Rewrite `h2` using `[mul_one]`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Apply the tactic sequence `ext <;> simp [h1, h2]`.

Use `set c := IsLocalization.mk' (FractionRing R) a b with hcdef`. Set `b' : nonZeroDivisors S` to `⟨_, hb'⟩`. Set `c' : FractionRing S` to `IsLocalization.mk' (FractionRing S) (e.symm (a, 0)) b'`. Establish `hΘc : Θ c' = (c, 0)`. Establish `hs` using `IsLocalization.mk'_spec (FractionRing S) (e.symm (a, 0)) b'`.

Establish `hs2` using `congrArg Θ hs`. Rewrite `hs2` using `[map_mul, hΘ, hΘ]`. Establish `hu` using `hg b'`. Establish `hcs` using `IsLocalization.mk'_spec (FractionRing R) a b`. Rewrite using `[← hu.mul_left_inj, hs2]`.

Rewrite using `[hgx, hgx]`. Simplify using `only [b', RingEquiv.apply_symm_apply, Prod.mk_mul_mk, map_zero, map_one, mul_one, zero_mul]`. Rewrite using `[hcs]`. Establish `hf : Function.Surjective ((RingHom.fst R S').comp e.toRingHom)`. Introduce `r`.

Conclude with `⟨e.symm (r, 0), by simp⟩`. Establish `hc' : IsIntegral S c'`. Take `⟨p, hpm, hp⟩` from `hc`. Take `⟨q, hqmap, -, hqm⟩` from `lifts_and_natDegree_eq_and_monic (f := (RingHom.fst R S').comp e.toRingHom) (p := p) ((lifts_iff_coeff_lifts p).mpr (fun n => hf _)) hpm`. Use `⟨X * q, monic_X.mul hqm, ?_⟩` and prove the remaining obligations.

Apply `hΘinj` to reduce the goal to its premises. Rewrite using `[Polynomial.hom_eval₂, map_zero, hΘc, eval₂_mul, eval₂_X]`. Establish `hfst : (RingHom.fst (FractionRing R) (FractionRing S')).comp (Θ.comp (algebraMap S (FractionRing S))) = (algebraMap R (FractionRing R)).comp ((RingHom.fst R S').comp e.toRingHom)`. Use extensionality with `x`. Simplify using `[hΘ, hgx]`.

Establish `h1 : (eval₂ (Θ.comp (algebraMap S (FractionRing S))) (c, 0) q).1 = 0`. Use `Polynomial.hom_eval₂ q (Θ.comp (algebraMap S (FractionRing S))) (RingHom.fst (FractionRing R) (FractionRing S')) (c, 0)` as an intermediate fact. Simplify using `only [RingHom.coe_fst] at this`. Rewrite using `[this, hfst, ← eval₂_map, hqmap]`. Conclude with `hp`.

Use `ext`. Simplify using `[h1]`. Simplify using the standard rewrite rules. Take `⟨s, hs⟩` from `hd c' hc'`. Use `⟨(e s).1, ?_⟩` and prove the remaining obligations.

Establish `h` using `congrArg (fun z => (Θ z).1) hs`. Simplify using `only [map_mul, hΘ, hΘc, hgx, Prod.fst_mul] at h`. Conclude with `h`.
-/
theorem conductor_prod_fst (R S' S : Type) [CommRing R] [CommRing S'] [CommRing S]
    (e : S ≃+* R × S') (d : S)
    (hd : ∀ c : FractionRing S, IsIntegral S c →
      ∃ s : S, algebraMap S (FractionRing S) s = algebraMap S (FractionRing S) d * c) :
    ∀ c : FractionRing R, IsIntegral R c →
      ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) (e d).1 * c := by
  intro c hc
  let g : S →+* FractionRing R × FractionRing S' :=
    (RingHom.prodMap (algebraMap R (FractionRing R)) (algebraMap S' (FractionRing S'))).comp
      e.toRingHom
  have hgx : ∀ x : S, g x = (algebraMap R (FractionRing R) (e x).1,
      algebraMap S' (FractionRing S') (e x).2) := fun x => rfl
  have hg : ∀ y : nonZeroDivisors S, IsUnit (g y) := by
    intro y
    rw [hgx, Prod.isUnit_iff]
    have h1 : (e y).1 ∈ nonZeroDivisors R := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      have h0 : e.symm (z, 0) * (y : S) = 0 := by
        apply e.injective
        rw [map_mul, RingEquiv.apply_symm_apply, map_zero]
        ext <;> simp [hz]
      have := (mul_right_mem_nonZeroDivisors_eq_zero_iff y.2).mp h0
      have := congrArg (fun w => (e w).1) this
      simpa using this
    have h2 : (e y).2 ∈ nonZeroDivisors S' := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      have h0 : e.symm (0, z) * (y : S) = 0 := by
        apply e.injective
        rw [map_mul, RingEquiv.apply_symm_apply, map_zero]
        ext <;> simp [hz]
      have := (mul_right_mem_nonZeroDivisors_eq_zero_iff y.2).mp h0
      have := congrArg (fun w => (e w).2) this
      simpa using this
    exact ⟨IsLocalization.map_units (FractionRing R) (⟨_, h1⟩ : nonZeroDivisors R),
      IsLocalization.map_units (FractionRing S') (⟨_, h2⟩ : nonZeroDivisors S')⟩
  let Θ : FractionRing S →+* FractionRing R × FractionRing S' := IsLocalization.lift hg
  have hΘ : ∀ x : S, Θ (algebraMap S (FractionRing S) x) = g x := fun x =>
    IsLocalization.lift_eq hg x
  have hΘinj : Function.Injective Θ := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h; rw [(IsFractionRing.injective S (FractionRing S)) h]
    · intro h
      have h' : e x = e y := by
        rw [hgx, hgx] at h
        ext
        · exact IsFractionRing.injective R (FractionRing R) (congrArg Prod.fst h)
        · exact IsFractionRing.injective S' (FractionRing S') (congrArg Prod.snd h)
      rw [e.injective h']

  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) c
  have hb' : e.symm ((b : R), (1 : S')) ∈ nonZeroDivisors S := by
    rw [mem_nonZeroDivisors_iff_right]
    intro z hz
    have hz' := congrArg e hz
    rw [map_mul, RingEquiv.apply_symm_apply, map_zero] at hz'
    have h1 : (e z).1 * b = 0 := congrArg Prod.fst hz'
    have h2 : (e z).2 * 1 = 0 := congrArg Prod.snd hz'
    rw [mul_right_mem_nonZeroDivisors_eq_zero_iff b.2] at h1
    rw [mul_one] at h2
    apply e.injective
    rw [map_zero]
    ext <;> simp [h1, h2]
  set c := IsLocalization.mk' (FractionRing R) a b with hcdef
  let b' : nonZeroDivisors S := ⟨_, hb'⟩
  let c' : FractionRing S := IsLocalization.mk' (FractionRing S) (e.symm (a, 0)) b'
  have hΘc : Θ c' = (c, 0) := by
    have hs := IsLocalization.mk'_spec (FractionRing S) (e.symm (a, 0)) b'
    have hs2 := congrArg Θ hs
    rw [map_mul, hΘ, hΘ] at hs2
    have hu := hg b'
    have hcs := IsLocalization.mk'_spec (FractionRing R) a b
    rw [← hu.mul_left_inj, hs2]
    rw [hgx, hgx]
    simp only [b', RingEquiv.apply_symm_apply, Prod.mk_mul_mk, map_zero, map_one, mul_one,
      zero_mul]
    rw [hcs]
  have hf : Function.Surjective ((RingHom.fst R S').comp e.toRingHom) := by
    intro r
    exact ⟨e.symm (r, 0), by simp⟩
  have hc' : IsIntegral S c' := by
    obtain ⟨p, hpm, hp⟩ := hc
    obtain ⟨q, hqmap, -, hqm⟩ := lifts_and_natDegree_eq_and_monic
      (f := (RingHom.fst R S').comp e.toRingHom) (p := p)
      ((lifts_iff_coeff_lifts p).mpr (fun n => hf _)) hpm
    refine ⟨X * q, monic_X.mul hqm, ?_⟩
    apply hΘinj
    rw [Polynomial.hom_eval₂, map_zero, hΘc, eval₂_mul, eval₂_X]
    have hfst : (RingHom.fst (FractionRing R) (FractionRing S')).comp
        (Θ.comp (algebraMap S (FractionRing S))) =
        (algebraMap R (FractionRing R)).comp ((RingHom.fst R S').comp e.toRingHom) := by
      ext x
      simp [hΘ, hgx]
    have h1 : (eval₂ (Θ.comp (algebraMap S (FractionRing S))) (c, 0) q).1 = 0 := by
      have := Polynomial.hom_eval₂ q (Θ.comp (algebraMap S (FractionRing S)))
        (RingHom.fst (FractionRing R) (FractionRing S')) (c, 0)
      simp only [RingHom.coe_fst] at this
      rw [this, hfst, ← eval₂_map, hqmap]
      exact hp
    ext
    · simp [h1]
    · simp
  obtain ⟨s, hs⟩ := hd c' hc'
  refine ⟨(e s).1, ?_⟩
  have h := congrArg (fun z => (Θ z).1) hs
  simp only [map_mul, hΘ, hΘc, hgx, Prod.fst_mul] at h
  exact h

end GlobalTheory
