import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.UnimodularGram.StarRingOfInvolution

namespace KStar.Cstarloc

variable {R : Type*} [CommRing R] [StarRing R] {M : Type*} [AddCommGroup M] [Module R M]

/- English proof (translation)
Take `⟨a, ha⟩` from `hR.norm_onto (h z z) hz (hh z z).symm`. Establish `hau : IsUnit a` using `isUnit_of_mul_isUnit_left (ha ▸ hz)`. Take `⟨u, rfl⟩` from `hau`. Use `⟨(↑u⁻¹ : R) • z, ?_⟩` and prove the remaining obligations. Simplify using `only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← ha]`.

Establish `h1 : (↑u⁻¹ : R) * ↑u = 1` using `Units.inv_mul u`. Establish `h2 : star (↑u⁻¹ : R) * star (↑u : R) = 1` using `by rw [← star_mul', Units.inv_mul, star_one]`. Take the linear combination `(star (↑u⁻¹ : R) * star (↑u : R)) * h1 + h2`.
-/
private theorem norm_one_of_unit (hR : UnramDatum R) (h : Sesq R M) (hh : IsHerm h) (z : M)
    (hz : IsUnit (h z z)) : ∃ x, h x x = 1 := by
  obtain ⟨a, ha⟩ := hR.norm_onto (h z z) hz (hh z z).symm
  have hau : IsUnit a := isUnit_of_mul_isUnit_left (ha ▸ hz)
  obtain ⟨u, rfl⟩ := hau
  refine ⟨(↑u⁻¹ : R) • z, ?_⟩
  simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← ha]
  have h1 : (↑u⁻¹ : R) * ↑u = 1 := Units.inv_mul u
  have h2 : star (↑u⁻¹ : R) * star (↑u : R) = 1 := by rw [← star_mul', Units.inv_mul, star_one]
  linear_combination (star (↑u⁻¹ : R) * star (↑u : R)) * h1 + h2

/- English proof (translation)
Take `⟨e, he⟩` from `hR.trace_one`. Set `b` to `Module.Free.chooseBasis R M`. Establish `: Nonempty (Module.Free.ChooseBasisIndex R M)` using `b.index_nonempty`. Take `⟨i⟩` from `this`. Take `⟨y, hy⟩` from `hu.2 (b.coord i)`.

Establish `hxy : h (b i) y = 1`. Use `LinearMap.congr_fun hy (b i)` as an intermediate fact. Simplify using `using this`. Establish `hyx : h y (b i) = 1` using `by rw [hh (b i) y, hxy, star_one]`. Distinguish the cases in `hx : IsUnit (h (b i) (b i))`.

Conclude with `norm_one_of_unit hR h hh _ hx`. Distinguish the cases in `hyy : IsUnit (h y y)`. Conclude with `norm_one_of_unit hR h hh _ hyy`. Use `norm_one_of_unit hR h hh (b i + e • y) ?_` and prove the remaining obligations. Establish `key : h (b i + e • y) (b i + e • y) = 1 + (h (b i) (b i) + e * star e * h y y)`.

Simplify using `only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hxy, hyx]`. Take the linear combination `he`. Establish `hw : ¬ IsUnit (e * star e * h y y)` using `fun hw => hyy (isUnit_of_mul_isUnit_right hw)`. Establish `hs : ¬ IsUnit (h (b i) (b i) + e * star e * h y y)` using `IsLocalRing.nonunits_add (mem_nonunits_iff.mpr hx) (mem_nonunits_iff.mpr hw)`. Rewrite using `[key]`.

Break down `IsLocalRing.isUnit_or_isUnit_of_add_one (show (1 + (h (b i) (b i) + e * star e * h y y)) + -(h (b i) (b i) + e * star e * h y y) = 1 by ring) with h' | h'` into its components or cases. Conclude with `h'`. Conclude with `absurd (by simpa using h'.neg) hs`.
-/
theorem exists_norm_one [IsLocalRing R] (hR : UnramDatum R) [Module.Free R M] [Nontrivial M]
    (h : Sesq R M) (hh : IsHerm h) (hu : IsUnimod h) : ∃ x, h x x = 1 := by
  obtain ⟨e, he⟩ := hR.trace_one
  let b := Module.Free.chooseBasis R M
  have : Nonempty (Module.Free.ChooseBasisIndex R M) := b.index_nonempty
  obtain ⟨i⟩ := this
  obtain ⟨y, hy⟩ := hu.2 (b.coord i)
  have hxy : h (b i) y = 1 := by
    have := LinearMap.congr_fun hy (b i)
    simpa using this
  have hyx : h y (b i) = 1 := by rw [hh (b i) y, hxy, star_one]
  by_cases hx : IsUnit (h (b i) (b i))
  · exact norm_one_of_unit hR h hh _ hx
  by_cases hyy : IsUnit (h y y)
  · exact norm_one_of_unit hR h hh _ hyy
  refine norm_one_of_unit hR h hh (b i + e • y) ?_
  have key : h (b i + e • y) (b i + e • y) = 1 + (h (b i) (b i) + e * star e * h y y) := by
    simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, hxy, hyx]
    linear_combination he
  have hw : ¬ IsUnit (e * star e * h y y) := fun hw => hyy (isUnit_of_mul_isUnit_right hw)
  have hs : ¬ IsUnit (h (b i) (b i) + e * star e * h y y) :=
    IsLocalRing.nonunits_add (mem_nonunits_iff.mpr hx) (mem_nonunits_iff.mpr hw)
  rw [key]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (show (1 + (h (b i) (b i) + e * star e * h y y)) + -(h (b i) (b i) + e * star e * h y y) = 1 by ring)
    with h' | h'
  · exact h'
  · exact absurd (by simpa using h'.neg) hs

/- English proof (translation)
Rewrite using `[mem_perp]`. Simplify using `[map_sub, map_smul, hx]`.
-/
private theorem sub_mem_perp (h : Sesq R M) (x : M) (hx : h x x = 1) (z : M) :
    z - h z x • x ∈ perp h x := by
  rw [mem_perp]
  simp [map_sub, map_smul, hx]

/- English proof (translation)
Establish `hperp : ∀ n ∈ perp h x, h x n = 0` using `fun n hn => by`. Rewrite `hn` using `[mem_perp]`. Rewrite using `[hh n x, hn, star_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `n1 n2 heq`.

Establish `hsub : ∀ m : perp h x, h m ((n1 : M) - n2) = 0` using `fun m => by`. Use `LinearMap.congr_fun heq m` as an intermediate fact. Simplify using `only [LinearMap.flip_apply, restr, LinearMap.domRestrict₁₂_apply] at this`. Rewrite using `[map_sub, this, sub_self]`. Establish `hxn : h x ((n1 : M) - n2) = 0` using `hperp _ (Submodule.sub_mem _ n1.2 n2.2)`.

Establish `hall : LinearMap.flip h ((n1 : M) - n2) = LinearMap.flip h 0`. Use extensionality with `z`. Simplify using `only [LinearMap.flip_apply, map_zero, LinearMap.zero_apply]`. Establish `hz` using `hsub ⟨z - h z x • x, sub_mem_perp h x hx z⟩`. Establish `hdec : h z = h (z - h z x • x) + h z x • h x`.

Rewrite using `[map_sub, map_smul, sub_add_cancel]`. Rewrite using `[hdec, LinearMap.add_apply, LinearMap.smul_apply, hxn, smul_zero, add_zero]`. Simplify using `using hz`. Conclude with `Subtype.ext (sub_eq_zero.mp (hu.1 hall))`. Introduce `f`.

Set `P : M →ₗ[R] perp h x` to `(LinearMap.id - (LinearMap.flip h x).smulRight x).codRestrict (perp h x) (fun z => by simpa using sub_mem_perp h x hx z)`. Take `⟨y, hy⟩` from `hu.2 (f ∘ₗ P)`. Establish `hPm : ∀ m : perp h x, P m = m` using `fun m => Subtype.ext (by simp [P, (mem_perp h x m).mp m.2])`. Establish `hPx : P x = 0` using `Subtype.ext (by simp [P, hx])`. Establish `h1 : h x y = 0`.

Use `LinearMap.congr_fun hy x` as an intermediate fact. Simplify `this` using `[hPx]`. Establish `hyx : h y x = 0` using `by rw [hh x y, h1, star_zero]`. Use `⟨⟨y, (mem_perp h x y).mpr hyx⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `m`.

Use `LinearMap.congr_fun hy m` as an intermediate fact. Simplify using `[restr, hPm] at this ⊢`. Conclude with `this`.
-/
theorem isUnimod_restr_perp (h : Sesq R M) (hh : IsHerm h) (hu : IsUnimod h) (x : M)
    (hx : h x x = 1) : IsUnimod (restr h (perp h x)) := by
  have hperp : ∀ n ∈ perp h x, h x n = 0 := fun n hn => by
    rw [mem_perp] at hn
    rw [hh n x, hn, star_zero]
  constructor
  · intro n1 n2 heq
    have hsub : ∀ m : perp h x, h m ((n1 : M) - n2) = 0 := fun m => by
      have := LinearMap.congr_fun heq m
      simp only [LinearMap.flip_apply, restr, LinearMap.domRestrict₁₂_apply] at this
      rw [map_sub, this, sub_self]
    have hxn : h x ((n1 : M) - n2) = 0 := hperp _ (Submodule.sub_mem _ n1.2 n2.2)
    have hall : LinearMap.flip h ((n1 : M) - n2) = LinearMap.flip h 0 := by
      ext z
      simp only [LinearMap.flip_apply, map_zero, LinearMap.zero_apply]
      have hz := hsub ⟨z - h z x • x, sub_mem_perp h x hx z⟩
      have hdec : h z = h (z - h z x • x) + h z x • h x := by
        rw [map_sub, map_smul, sub_add_cancel]
      rw [hdec, LinearMap.add_apply, LinearMap.smul_apply, hxn, smul_zero, add_zero]
      simpa using hz
    exact Subtype.ext (sub_eq_zero.mp (hu.1 hall))
  · intro f
    let P : M →ₗ[R] perp h x := (LinearMap.id - (LinearMap.flip h x).smulRight x).codRestrict (perp h x)
      (fun z => by simpa using sub_mem_perp h x hx z)
    obtain ⟨y, hy⟩ := hu.2 (f ∘ₗ P)
    have hPm : ∀ m : perp h x, P m = m := fun m => Subtype.ext (by simp [P, (mem_perp h x m).mp m.2])
    have hPx : P x = 0 := Subtype.ext (by simp [P, hx])
    have h1 : h x y = 0 := by
      have := LinearMap.congr_fun hy x
      simpa [hPx] using this
    have hyx : h y x = 0 := by rw [hh x y, h1, star_zero]
    refine ⟨⟨y, (mem_perp h x y).mpr hyx⟩, ?_⟩
    ext m
    have := LinearMap.congr_fun hy m
    simp [restr, hPm] at this ⊢
    exact this

end KStar.Cstarloc
