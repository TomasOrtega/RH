import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMassConstOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandA

noncomputable section

namespace Formalism.MainNotions.BridgeLemVR

open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_loc_iff (p : Ideal (𝓞 K)) (N : Submodule (𝓞 K) K) (x : K) :
    x ∈ loc (K := K) p N ↔ ∃ s ∈ hcompl (K := K) p, s • x ∈ N := Iff.rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_locR_iff (p : Ideal (𝓞 K)) (x : K) :
    x ∈ locR (K := K) p ↔ ∃ s ∈ hcompl (K := K) p, s • x ∈ (1 : Submodule (𝓞 K) K) := Iff.rfl

/- English proof (translation)
Use `hp.isPrime` as an intermediate fact. Unfold `hcompl`. Rewrite using `[Submonoid.closure_le]`. Introduce `s hs`. Conclude with `hs.1`.
-/
theorem hcompl_le_primeCompl {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    hcompl (K := K) p ≤ p.primeCompl := by
  have := hp.isPrime
  unfold hcompl
  rw [Submonoid.closure_le]
  intro s hs
  exact hs.1

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, (hcompl (K := K) p).one_mem, by rw [one_smul]; exact Submodule.mem_one.2 ⟨1, map_one _⟩⟩`.
-/
theorem one_mem_locR (p : Ideal (𝓞 K)) : (1 : K) ∈ locR (K := K) p :=
  ⟨1, (hcompl (K := K) p).one_mem, by rw [one_smul]; exact Submodule.mem_one.2 ⟨1, map_one _⟩⟩

/- English proof (translation)
Take `⟨s, hs, hsx⟩` from `hx`. Take `⟨t, ht, hty⟩` from `hy`. Use `⟨s * t, (hcompl (K := K) p).mul_mem hs ht, ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `Submodule.mem_one.1 hsx`. Take `⟨r', hr'⟩` from `Submodule.mem_one.1 hty`.

Use `Submodule.mem_one.2 ⟨r * r', ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hr, hr', Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_mem_locR {p : Ideal (𝓞 K)} {x y : K} (hx : x ∈ locR (K := K) p) (hy : y ∈ locR (K := K) p) :
    x * y ∈ locR (K := K) p := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  refine ⟨s * t, (hcompl (K := K) p).mul_mem hs ht, ?_⟩
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 hsx
  obtain ⟨r', hr'⟩ := Submodule.mem_one.1 hty
  refine Submodule.mem_one.2 ⟨r * r', ?_⟩
  rw [map_mul, hr, hr', Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
  ring

/- English proof (translation)
Establish `key : hcompl (K` using `K) p ≤ (hcompl (K := K) p).comap (conjO K : 𝓞 K →* 𝓞 K) := by conv_lhs => unfold hcompl`. Rewrite using `[Submonoid.closure_le]`. Introduce `s hs`. Use `show conjO K s ∈ hcompl (K := K) p`. Apply `Submonoid.subset_closure` to reduce the goal to its premises.

Use `⟨hs.2 (conjO K s) rfl, fun t ht => ?_⟩` and prove the remaining obligations. Establish `e : t = s`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `: (t : K) = star (star (s : K))` using `ht`. Rewrite `this` using `[star_star]`.

Conclude with `this`. Rewrite using `[e]`. Conclude with `hs.1`. Conclude with `key hs`.
-/
theorem conjO_mem_hcompl {p : Ideal (𝓞 K)} {s : 𝓞 K} (hs : s ∈ hcompl (K := K) p) :
    conjO K s ∈ hcompl (K := K) p := by
  have key : hcompl (K := K) p ≤ (hcompl (K := K) p).comap (conjO K : 𝓞 K →* 𝓞 K) := by
    conv_lhs => unfold hcompl
    rw [Submonoid.closure_le]
    intro s hs
    show conjO K s ∈ hcompl (K := K) p
    apply Submonoid.subset_closure
    refine ⟨hs.2 (conjO K s) rfl, fun t ht => ?_⟩
    have e : t = s := by
      apply RingOfIntegers.ext
      have : (t : K) = star (star (s : K)) := ht
      rw [star_star] at this
      exact this
    rw [e]
    exact hs.1
  exact key hs

/- English proof (translation)
Take `⟨s, hs, hsx⟩` from `hx`. Use `⟨conjO K s, conjO_mem_hcompl hs, ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `Submodule.mem_one.1 hsx`. Use `Submodule.mem_one.2 ⟨conjO K r, ?_⟩` and prove the remaining obligations. Rewrite `hr`, the goal using `[Algebra.smul_def]`.

Establish `e1 : algebraMap (𝓞 K) K (conjO K r) = star (algebraMap (𝓞 K) K r)` using `rfl`. Establish `e2 : algebraMap (𝓞 K) K (conjO K s) = star (algebraMap (𝓞 K) K s)` using `rfl`. Rewrite using `[e1, e2, hr, star_mul']`.
-/
theorem star_mem_locR {p : Ideal (𝓞 K)} {x : K} (hx : x ∈ locR (K := K) p) :
    star x ∈ locR (K := K) p := by
  obtain ⟨s, hs, hsx⟩ := hx
  refine ⟨conjO K s, conjO_mem_hcompl hs, ?_⟩
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 hsx
  refine Submodule.mem_one.2 ⟨conjO K r, ?_⟩
  rw [Algebra.smul_def] at hr ⊢
  have e1 : algebraMap (𝓞 K) K (conjO K r) = star (algebraMap (𝓞 K) K r) := rfl
  have e2 : algebraMap (𝓞 K) K (conjO K s) = star (algebraMap (𝓞 K) K s) := rfl
  rw [e1, e2, hr, star_mul']

/- English proof (translation)
Set `J : Ideal (𝓞 K)` to `(1 : Submodule (𝓞 K) K).comap (LinearMap.toSpanSingleton (𝓞 K) K x)`. Establish `hJ : J = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨p, hp, hJp⟩` from `Ideal.exists_le_maximal J hne`. Take `⟨s, hs, hsx⟩` from `hx p hp`.

Establish `hsJ : s ∈ J` using `by show LinearMap.toSpanSingleton (𝓞 K) K x s ∈ (1 : Submodule (𝓞 K) K)`. Rewrite using `[LinearMap.toSpanSingleton_apply]`. Conclude with `hsx`. Conclude with `hcompl_le_primeCompl hp hs (hJp hsJ)`. Establish `h1 : (1 : 𝓞 K) ∈ J` using `hJ ▸ Submodule.mem_top`.

Express the relevant statement in the definitionally equal form `LinearMap.toSpanSingleton (𝓞 K) K x 1 ∈ (1 : Submodule (𝓞 K) K) at h1`. Rewrite `h1` using `[LinearMap.toSpanSingleton_apply, one_smul]`. Then use the resulting hypothesis.
-/
theorem mem_one_of_locR {x : K} (hx : ∀ p : Ideal (𝓞 K), p.IsMaximal → x ∈ locR (K := K) p) :
    x ∈ (1 : Submodule (𝓞 K) K) := by
  let J : Ideal (𝓞 K) := (1 : Submodule (𝓞 K) K).comap (LinearMap.toSpanSingleton (𝓞 K) K x)
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hJp⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨s, hs, hsx⟩ := hx p hp
    have hsJ : s ∈ J := by
      show LinearMap.toSpanSingleton (𝓞 K) K x s ∈ (1 : Submodule (𝓞 K) K)
      rw [LinearMap.toSpanSingleton_apply]
      exact hsx
    exact hcompl_le_primeCompl hp hs (hJp hsJ)
  have h1 : (1 : 𝓞 K) ∈ J := hJ ▸ Submodule.mem_top
  change LinearMap.toSpanSingleton (𝓞 K) K x 1 ∈ (1 : Submodule (𝓞 K) K) at h1
  rwa [LinearMap.toSpanSingleton_apply, one_smul] at h1

/- English proof (translation)
Take `⟨g, hg, hgM⟩` from `hM.2 p hp`. Use `⟨g 1, (mem_isom_iff h1 g).1 hg, fun y => ?_⟩` and prove the remaining obligations. Establish `hgx : ∀ x, g x = x * g 1`. Introduce `x`. Establish `: g x = g (x • (1 : K))` using `by simp`.

Rewrite using `[this, map_smul, smul_eq_mul]`. Rewrite using `[← hgM, mem_gmap]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `⟨g.symm y, hy, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hgx, LinearEquiv.apply_symm_apply]`. Introduce and unpack `⟨r, hr, rfl⟩`. Rewrite using `[← hgx, LinearEquiv.symm_apply_apply]`. Conclude with `hr`.
-/
theorem exists_local (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0) {M : Submodule (𝓞 K) K}
    (hM : M ∈ genus h (1 : Submodule (𝓞 K) K)) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    ∃ z : K, star z * z = 1 ∧ ∀ y : K, y ∈ loc (K := K) p M ↔ ∃ r ∈ locR (K := K) p, y = r * z := by
  obtain ⟨g, hg, hgM⟩ := hM.2 p hp
  refine ⟨g 1, (mem_isom_iff h1 g).1 hg, fun y => ?_⟩
  have hgx : ∀ x, g x = x * g 1 := by
    intro x
    have : g x = g (x • (1 : K)) := by simp
    rw [this, map_smul, smul_eq_mul]
  rw [← hgM, mem_gmap]
  constructor
  · intro hy
    refine ⟨g.symm y, hy, ?_⟩
    rw [← hgx, LinearEquiv.apply_symm_apply]
  · rintro ⟨r, hr, rfl⟩
    rw [← hgx, LinearEquiv.symm_apply_apply]
    exact hr

/- English proof (translation)
Establish `key : ∀ p : Ideal (𝓞 K), p.IsMaximal → a * star a ∈ locR (K` using `K) p ∧ (a * star a)⁻¹ ∈ locR (K := K) p := by`. Introduce `p hp`. Take `⟨z, hz, hzM⟩` from `exists_local h h1 hM hp`. Take `⟨z', hz', hzM'⟩` from `exists_local h h1 hM' hp`. Establish `hl : loc (K` using `K) p M = Submodule.span (𝓞 K) {a} * loc (K := K) p M' := by`.

Rewrite using `[he, loc_mul hp]`. Establish `hzin : z ∈ loc (K` using `K) p M := (hzM z).2 ⟨1, one_mem_locR p, (one_mul z).symm⟩`. Rewrite `hzin` using `[hl, Submodule.mem_span_singleton_mul]`. Take `⟨m, hm, hmz⟩` from `hzin`. Take `⟨r, hr, rfl⟩` from `(hzM' m).1 hm`.

Establish `haz : a * z' ∈ loc (K` using `K) p M := by`. Rewrite using `[hl, Submodule.mem_span_singleton_mul]`. Conclude with `⟨z', (hzM' z').2 ⟨1, one_mem_locR p, (one_mul z').symm⟩, rfl⟩`. Take `⟨r', hr', hr'e⟩` from `(hzM _).1 haz`. Establish `hz1 : z * star z = 1` using `by rw [mul_comm]; exact hz`.

Establish `hz1' : z' * star z' = 1` using `by rw [mul_comm]; exact hz'`. Establish `t1` using `congrArg (fun t => t * star t) hr'e`. Simplify using `only [star_mul'] at t1`. Establish `e1 : a * star a = r' * star r'`. Take the linear combination `t1 - (a * star a) * hz1' + (r' * star r') * hz1`.

Establish `t2` using `congrArg (fun t => t * star t) hmz`. Simplify using `only [star_mul'] at t2`. Establish `e2 : a * star a * (r * star r) = 1`. Take the linear combination `t2 - (a * star a * r * star r) * hz1' + hz1`. Use `⟨e1 ▸ mul_mem_locR hr' (star_mem_locR hr'), ?_⟩` and prove the remaining obligations.

Rewrite using `[inv_eq_of_mul_eq_one_right e2]`. Conclude with `mul_mem_locR hr (star_mem_locR hr)`. Conclude with `⟨mem_one_of_locR fun p hp => (key p hp).1, mem_one_of_locR fun p hp => (key p hp).2⟩`.
-/
theorem norm_unit (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0) {M M' : Submodule (𝓞 K) K}
    (hM : M ∈ genus h (1 : Submodule (𝓞 K) K)) (hM' : M' ∈ genus h (1 : Submodule (𝓞 K) K)) {a : K}
    (he : M = Submodule.span (𝓞 K) {a} * M') :
    a * star a ∈ (1 : Submodule (𝓞 K) K) ∧ (a * star a)⁻¹ ∈ (1 : Submodule (𝓞 K) K) := by
  have key : ∀ p : Ideal (𝓞 K), p.IsMaximal →
      a * star a ∈ locR (K := K) p ∧ (a * star a)⁻¹ ∈ locR (K := K) p := by
    intro p hp
    obtain ⟨z, hz, hzM⟩ := exists_local h h1 hM hp
    obtain ⟨z', hz', hzM'⟩ := exists_local h h1 hM' hp
    have hl : loc (K := K) p M = Submodule.span (𝓞 K) {a} * loc (K := K) p M' := by
      rw [he, loc_mul hp]
    have hzin : z ∈ loc (K := K) p M := (hzM z).2 ⟨1, one_mem_locR p, (one_mul z).symm⟩
    rw [hl, Submodule.mem_span_singleton_mul] at hzin
    obtain ⟨m, hm, hmz⟩ := hzin
    obtain ⟨r, hr, rfl⟩ := (hzM' m).1 hm
    have haz : a * z' ∈ loc (K := K) p M := by
      rw [hl, Submodule.mem_span_singleton_mul]
      exact ⟨z', (hzM' z').2 ⟨1, one_mem_locR p, (one_mul z').symm⟩, rfl⟩
    obtain ⟨r', hr', hr'e⟩ := (hzM _).1 haz
    have hz1 : z * star z = 1 := by rw [mul_comm]; exact hz
    have hz1' : z' * star z' = 1 := by rw [mul_comm]; exact hz'
    have t1 := congrArg (fun t => t * star t) hr'e
    simp only [star_mul'] at t1
    have e1 : a * star a = r' * star r' := by
      linear_combination t1 - (a * star a) * hz1' + (r' * star r') * hz1
    have t2 := congrArg (fun t => t * star t) hmz
    simp only [star_mul'] at t2
    have e2 : a * star a * (r * star r) = 1 := by
      linear_combination t2 - (a * star a * r * star r) * hz1' + hz1
    refine ⟨e1 ▸ mul_mem_locR hr' (star_mem_locR hr'), ?_⟩
    rw [inv_eq_of_mul_eq_one_right e2]
    exact mul_mem_locR hr (star_mem_locR hr)
  exact ⟨mem_one_of_locR fun p hp => (key p hp).1, mem_one_of_locR fun p hp => (key p hp).2⟩

end Formalism.MainNotions.BridgeLemVR

end
