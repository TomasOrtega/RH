import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuSurjPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.LeafKumMuSurjPf

namespace LateralTheory.E.H2CurveOrder.LeafKumMuSurjPowPf

def powCof {A : Type*} [CommRing A] (u v : A) (q : ℕ) : A := ∑ i ∈ Finset.range q, u ^ i * v ^ (q - 1 - i)

/- English proof (translation)
The claim follows from `geom_sum₂_mul u v q`.
-/
theorem powCof_mul {A : Type*} [CommRing A] (u v : A) (q : ℕ) : powCof u v q * (u - v) = u ^ q - v ^ q :=
  geom_sum₂_mul u v q

/- English proof (translation)
Simplify using `[powCof, map_sum, map_mul, map_pow]`.
-/
theorem powCof_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (u v : A) (q : ℕ) :
    φ (powCof u v q) = powCof (φ u) (φ v) q := by
  simp [powCof, map_sum, map_mul, map_pow]

/- English proof (translation)
Unfold `powCof`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => v ^ (q - 1))]`. Simplify using the standard rewrite rules. Introduce `i hi`. Rewrite using `[← pow_add]`.

Use `congr 1`. Use `Finset.mem_range.1 hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem powCof_self {A : Type*} [CommRing A] (v : A) (q : ℕ) : powCof v v q = (q : A) * v ^ (q - 1) := by
  unfold powCof
  rw [Finset.sum_congr rfl (g := fun _ => v ^ (q - 1))]
  · simp
  · intro i hi
    rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega

/- English proof (translation)
Establish `: NeZero (q : K)` using `⟨hq⟩`. Establish `hroot : Polynomial.IsRoot (Polynomial.cyclotomic q K) z`. Rewrite using `[← Polynomial.map_cyclotomic_int, Polynomial.IsRoot, Polynomial.eval_map]`. Rewrite `hz` using `[Polynomial.aeval_def, algebraMap_int_eq]`. Conclude with `hz`.

Establish `hp : IsPrimitiveRoot z q` using `(Polynomial.isRoot_cyclotomic_iff).1 hroot`. Take `⟨i, hi, hzi⟩` from `hp.eq_pow_of_pow_eq_one hw`. Use `⟨⟨i, hi⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hzi, powCof_self]`. Establish `hz0 : z ≠ 0` using `fun h => by`.

Use `hp.pow_eq_one` as an intermediate fact. Rewrite `this` using `[h, zero_pow (NeZero.ne q)]`. Conclude with `zero_ne_one this`. Conclude with `mul_ne_zero hq (pow_ne_zero _ (pow_ne_zero _ hz0))`.
-/
theorem field_step {K : Type} [Field K] (q : ℕ) [NeZero q] (hq : (q : K) ≠ 0) (z w : K)
    (hz : Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0) (hw : w ^ q = 1) :
    ∃ a : Fin q, powCof w (z ^ (a : ℕ)) q ≠ 0 := by
  have : NeZero (q : K) := ⟨hq⟩
  have hroot : Polynomial.IsRoot (Polynomial.cyclotomic q K) z := by
    rw [← Polynomial.map_cyclotomic_int, Polynomial.IsRoot, Polynomial.eval_map]
    rw [Polynomial.aeval_def, algebraMap_int_eq] at hz
    exact hz
  have hp : IsPrimitiveRoot z q := (Polynomial.isRoot_cyclotomic_iff).1 hroot
  obtain ⟨i, hi, hzi⟩ := hp.eq_pow_of_pow_eq_one hw
  refine ⟨⟨i, hi⟩, ?_⟩
  rw [← hzi, powCof_self]
  have hz0 : z ≠ 0 := fun h => by
    have := hp.pow_eq_one; rw [h, zero_pow (NeZero.ne q)] at this; exact zero_ne_one this
  exact mul_ne_zero hq (pow_ne_zero _ (pow_ne_zero _ hz0))

/- English proof (translation)
Apply `V.toRingedSpace.isUnit_of_isUnit_germ` to reduce the goal to its premises. Introduce `x hx`. Establish `hx' : x ∈ V.basicOpen t` using `by rw [h]; trivial`. Conclude with `(V.mem_basicOpen_top t x).1 hx'`.
-/
theorem isUnit_of_basicOpen_top {V : Scheme.{0}} (t : Γ(V, ⊤)) (h : V.basicOpen t = ⊤) : IsUnit t := by
  apply V.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  have hx' : x ∈ V.basicOpen t := by rw [h]; trivial
  exact (V.mem_basicOpen_top t x).1 hx'

/- English proof (translation)
Introduce `q _ U ζ u hu`. Set `s : Fin q → Γ(U, ⊤)` to `fun a => powCof (u : Γ(U, ⊤)) (ζ.1 ^ (a : ℕ)) q`. Establish `hcov : TopologicalSpace.IsOpenCover (fun a => U.basicOpen (s a))`. Rewrite using `[TopologicalSpace.IsOpenCover, eq_top_iff]`. Introduce and unpack `x -`.

Rewrite using `[TopologicalSpace.Opens.mem_iSup]`. Set `φ` to `(U.Γevaluation x).hom`. Establish `hq : (q : U.residueField x) ≠ 0`. Use `ζ.2.1.map φ` as an intermediate fact. Simplify using `using this.ne_zero`.

Establish `hz : Polynomial.aeval (φ ζ.1) (Polynomial.cyclotomic q ℤ) = 0`. Use `Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ.1 (Polynomial.cyclotomic q ℤ)` as an intermediate fact. Rewrite `this` using `[ζ.2.2, map_zero]`. Conclude with `this`. Establish `hw : (φ (u : Γ(U, ⊤))) ^ q = 1`.

Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]`. Take `⟨a, ha⟩` from `field_step q hq _ _ hz hw`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.evaluation_ne_zero_iff_mem_basicOpen (X := U) (U := ⊤) x trivial]`. Use `show φ (s a) ≠ 0`.

Simplify using `only [s]`. Rewrite using `[powCof_map, map_pow]`. Conclude with `ha`. Set `𝒰` to `U.openCoverOfIsOpenCover _ hcov`. Use `⟨Sieve.ofArrows 𝒰.X 𝒰.f, Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology 𝒰), ?_⟩` and prove the remaining obligations.

Introduce `V f hf`. Take `⟨a', g, rfl⟩` from `(Sieve.mem_ofArrows_iff _ _ _).1 hf`. Set `a : Fin q` to `a'`. Use `⟨(a : ℕ), ?_⟩` and prove the remaining obligations. Establish `hunit : IsUnit ((g ≫ 𝒰.f a).appTop (s a))`.

Apply `isUnit_of_basicOpen_top` to reduce the goal to its premises. Rewrite using `[← Scheme.preimage_basicOpen_top, eq_top_iff]`. Introduce `x _`. Use `show (U.basicOpen (s a)).ι.base (g.base x) ∈ U.basicOpen (s a)`. Conclude with `(g.base x).2`.

Establish `hzero : s a * ((u : Γ(U, ⊤)) - ζ.1 ^ (a : ℕ)) = 0`. Simplify using `only [s]`. Rewrite using `[powCof_mul, ← Units.val_pow_eq_pow_val, hu, Units.val_one, ← pow_mul, mul_comm, pow_mul, prim_pow_q ζ, one_pow, sub_self]`. Establish `key : ∀ ψ : Γ(U, ⊤) →+* Γ(V, ⊤), IsUnit (ψ (s a)) → ψ u = ψ ζ.1 ^ (a : ℕ)` using `fun ψ h => by`. Establish `h2` using `congrArg ψ hzero`.

Rewrite `h2` using `[map_mul, map_zero]`. Rewrite using `[← map_pow]`. Conclude with `sub_eq_zero.1 ((h.mul_right_eq_zero).1 (by rw [← map_sub]; exact h2))`. Apply `key` to reduce the goal to its premises. Conclude with `hunit`.
-/
theorem pow_pf : LeafKumMuSurjPow := by
  intro q _ U ζ u hu
  let s : Fin q → Γ(U, ⊤) := fun a => powCof (u : Γ(U, ⊤)) (ζ.1 ^ (a : ℕ)) q
  have hcov : TopologicalSpace.IsOpenCover (fun a => U.basicOpen (s a)) := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    rintro x -
    rw [TopologicalSpace.Opens.mem_iSup]
    let φ := (U.Γevaluation x).hom
    have hq : (q : U.residueField x) ≠ 0 := by
      have := ζ.2.1.map φ
      simpa using this.ne_zero
    have hz : Polynomial.aeval (φ ζ.1) (Polynomial.cyclotomic q ℤ) = 0 := by
      have := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ.1 (Polynomial.cyclotomic q ℤ)
      rw [ζ.2.2, map_zero] at this
      exact this
    have hw : (φ (u : Γ(U, ⊤))) ^ q = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]
    obtain ⟨a, ha⟩ := field_step q hq _ _ hz hw
    refine ⟨a, ?_⟩
    rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen (X := U) (U := ⊤) x trivial]
    show φ (s a) ≠ 0
    simp only [s]
    rw [powCof_map, map_pow]
    exact ha
  let 𝒰 := U.openCoverOfIsOpenCover _ hcov
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f,
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology 𝒰), ?_⟩
  intro V f hf
  obtain ⟨a', g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
  let a : Fin q := a'
  refine ⟨(a : ℕ), ?_⟩
  have hunit : IsUnit ((g ≫ 𝒰.f a).appTop (s a)) := by
    apply isUnit_of_basicOpen_top
    rw [← Scheme.preimage_basicOpen_top, eq_top_iff]
    intro x _
    show (U.basicOpen (s a)).ι.base (g.base x) ∈ U.basicOpen (s a)
    exact (g.base x).2
  have hzero : s a * ((u : Γ(U, ⊤)) - ζ.1 ^ (a : ℕ)) = 0 := by
    simp only [s]
    rw [powCof_mul, ← Units.val_pow_eq_pow_val, hu, Units.val_one, ← pow_mul, mul_comm, pow_mul,
      prim_pow_q ζ, one_pow, sub_self]
  have key : ∀ ψ : Γ(U, ⊤) →+* Γ(V, ⊤), IsUnit (ψ (s a)) → ψ u = ψ ζ.1 ^ (a : ℕ) := fun ψ h => by
    have h2 := congrArg ψ hzero
    rw [map_mul, map_zero] at h2
    rw [← map_pow]
    exact sub_eq_zero.1 ((h.mul_right_eq_zero).1 (by rw [← map_sub]; exact h2))
  apply key
  exact hunit

/- English proof (translation)
The claim follows from `pow_pf`.
-/
theorem LeafKumMuSurjPow_of : LeafKumMuSurjPow := pow_pf

end LateralTheory.E.H2CurveOrder.LeafKumMuSurjPowPf
