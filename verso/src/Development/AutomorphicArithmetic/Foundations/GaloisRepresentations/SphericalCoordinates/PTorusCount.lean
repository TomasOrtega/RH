import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

/- English proof (translation)
Use `haveI := ZLattice.module_free ℝ Lz`. Use `haveI := ZLattice.module_finite ℝ Lz`. Set `b` to `Module.Free.chooseBasis ℤ Lz`. Set `bR` to `Module.Basis.ofZLatticeBasis ℝ Lz b`. Rewrite using `[← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix bR, ← eq_intCast (Int.castRingHom ℝ), RingHom.map_det]`.

Use `congr 1`. Use extensionality with `i j`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, Module.Basis.ofZLatticeBasis_apply, ← hfL, Module.Basis.ofZLatticeBasis_repr_apply]`. Both sides reduce to the same expression.
-/
private theorem det_lattice_restrict_eq_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Lz : Submodule ℤ E) [DiscreteTopology Lz] [IsZLattice ℝ Lz]
    (f : E →ₗ[ℝ] E) (fL : Lz →ₗ[ℤ] Lz) (hfL : ∀ x, (fL x : E) = f x) :
    ((LinearMap.det fL : ℤ) : ℝ) = LinearMap.det f := by
  haveI := ZLattice.module_free ℝ Lz
  haveI := ZLattice.module_finite ℝ Lz
  let b := Module.Free.chooseBasis ℤ Lz
  let bR := Module.Basis.ofZLatticeBasis ℝ Lz b
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix bR, ← eq_intCast (Int.castRingHom ℝ),
    RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    Module.Basis.ofZLatticeBasis_apply, ← hfL, Module.Basis.ofZLatticeBasis_repr_apply]
  rfl

/- English proof (translation)
Set `Lz : Submodule ℤ E` to `AddSubgroup.toIntSubmodule L`. Use `haveI : DiscreteTopology Lz := hd`. Use `haveI : IsZLattice ℝ Lz := ⟨hs⟩`. Use `haveI := ZLattice.module_free ℝ Lz`. Use `haveI := ZLattice.module_finite ℝ Lz`.

Set `fL : Lz →ₗ[ℤ] Lz` to `{ toFun := fun x => ⟨f x, hf x x.2⟩ map_add' := by intro x y; ext; simp map_smul' := by intro c x; ext; simp }`. Establish `hfL : ∀ x, (fL x : E) = f x` using `fun x => rfl`. Establish `hdetZ` using `det_lattice_restrict_eq_det Lz f fL hfL`. Establish `hdetL : LinearMap.det fL ≠ 0`. Introduce `h`.

Apply `hdet` to reduce the goal to its premises. Rewrite using `[← hdetZ, h]`. Simplify using the standard rewrite rules. Set `fe` to `LinearMap.equivOfDetNeZero f hdet`. Establish `hfe : ∀ z, fe z = f z` using `fun z => rfl`.

Establish `finj : Function.Injective f`. Introduce `x y h`. Apply `fe.injective` to reduce the goal to its premises. Rewrite using `[hfe, hfe, h]`. Establish `hinj : Function.Injective fL` using `fun x y h => Subtype.ext (finj (congrArg Subtype.val h))`.

Set `N` to `LinearMap.range fL`. Set `e` to `LinearEquiv.ofInjective fL hinj`. Establish `hcard` using `Submodule.natAbs_det_equiv N e`. Establish `hcomp : N.subtype ∘ₗ (e : Lz →+ N).toIntLinearMap = fL` using `by ext x; rfl`. Rewrite `hcard` using `[hcomp]`.

Use `haveI : Finite (Lz ⧸ N) := Nat.finite_of_card_ne_zero (by rw [← hcard]; exact Int.natAbs_ne_zero.mpr hdetL)`. Use `letI := Fintype.ofFinite (Lz ⧸ N)`. Set `s : (Lz ⧸ N) → E` to `fun q => fe.symm ((Quotient.out q : Lz) : E)`. Establish `hs_f : ∀ q, f (s q) = ((Quotient.out q : Lz) : E)` using `fun q => by`. Rewrite using `[← hfe]`.

Conclude with `fe.apply_symm_apply _`. Establish `hsinj : Function.Injective s`. Introduce `q q' h`. Establish `h1 : (Quotient.out q : Lz) = Quotient.out q'` using `Subtype.ext (by rw [← hs_f, ← hs_f, h])`. Rewrite using `[← Submodule.Quotient.mk_out q, ← Submodule.Quotient.mk_out q', h1]`.

Establish `key : ∀ z (hz : f z ∈ L) (q' : Lz ⧸ N), z - s q' ∈ L ↔ q' = Submodule.Quotient.mk (⟨f z, hz⟩ : Lz)`. Introduce `z hz q'`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hm : (⟨f z, hz⟩ : Lz) - Quotient.out q' ∈ N` using `⟨⟨z - s q', h⟩, by ext; simp [fL, hs_f]⟩`.

Rewrite `hm` using `[← Submodule.Quotient.eq, Submodule.Quotient.mk_out]`. Conclude with `hm.symm`. Introduce `h`. Establish `hm : (⟨f z, hz⟩ : Lz) - Quotient.out q' ∈ N`. Rewrite using `[← Submodule.Quotient.eq, Submodule.Quotient.mk_out, h]`.

Take `⟨l, hl⟩` from `hm`. Establish `: f (l : E) = f (z - s q')`. Rewrite using `[← hfL, hl, map_sub, hs_f]`. Both sides reduce to the same expression. Rewrite using `[← finj this]`.

Conclude with `l.2`. Use `⟨Finset.univ.image s, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Take `⟨q, _, rfl⟩` from `Finset.mem_image.mp hz`. Rewrite using `[hs_f]`.

Conclude with `(Quotient.out q).2`. Introduce `z hz`. Use `⟨s (Submodule.Quotient.mk (⟨f z, hz⟩ : Lz)), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key z hz _).mpr rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `z' ⟨hz', hzz'⟩`. Take `⟨q, _, rfl⟩` from `Finset.mem_image.mp hz'`.

Rewrite using `[(key z hz q).mp hzz']`. Rewrite using `[Finset.card_image_of_injective _ hsinj, Finset.card_univ, ← Nat.card_eq_fintype_card, ← hcard, ← hdetZ, Nat.cast_natAbs, Int.cast_abs]`.
-/
private theorem exists_lattice_reps {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : AddSubgroup E) (hd : DiscreteTopology L)
    (hs : Submodule.span ℝ (L : Set E) = ⊤) (f : E →ₗ[ℝ] E) (hf : ∀ z ∈ L, f z ∈ L)
    (hdet : LinearMap.det f ≠ 0) :
    ∃ Fz : Finset E, (∀ z ∈ Fz, f z ∈ L) ∧ (∀ z, f z ∈ L → ∃! z', z' ∈ Fz ∧ z - z' ∈ L) ∧
      (Fz.card : ℝ) = |LinearMap.det f| := by
  classical
  let Lz : Submodule ℤ E := AddSubgroup.toIntSubmodule L
  haveI : DiscreteTopology Lz := hd
  haveI : IsZLattice ℝ Lz := ⟨hs⟩
  haveI := ZLattice.module_free ℝ Lz
  haveI := ZLattice.module_finite ℝ Lz
  let fL : Lz →ₗ[ℤ] Lz :=
    { toFun := fun x => ⟨f x, hf x x.2⟩
      map_add' := by intro x y; ext; simp
      map_smul' := by intro c x; ext; simp }
  have hfL : ∀ x, (fL x : E) = f x := fun x => rfl
  have hdetZ := det_lattice_restrict_eq_det Lz f fL hfL
  have hdetL : LinearMap.det fL ≠ 0 := by
    intro h; apply hdet; rw [← hdetZ, h]; simp
  let fe := LinearMap.equivOfDetNeZero f hdet
  have hfe : ∀ z, fe z = f z := fun z => rfl
  have finj : Function.Injective f := by
    intro x y h; apply fe.injective; rw [hfe, hfe, h]
  have hinj : Function.Injective fL := fun x y h => Subtype.ext (finj (congrArg Subtype.val h))
  let N := LinearMap.range fL
  let e := LinearEquiv.ofInjective fL hinj
  have hcard := Submodule.natAbs_det_equiv N e
  have hcomp : N.subtype ∘ₗ (e : Lz →+ N).toIntLinearMap = fL := by ext x; rfl
  rw [hcomp] at hcard
  haveI : Finite (Lz ⧸ N) :=
    Nat.finite_of_card_ne_zero (by rw [← hcard]; exact Int.natAbs_ne_zero.mpr hdetL)
  letI := Fintype.ofFinite (Lz ⧸ N)
  let s : (Lz ⧸ N) → E := fun q => fe.symm ((Quotient.out q : Lz) : E)
  have hs_f : ∀ q, f (s q) = ((Quotient.out q : Lz) : E) := fun q => by
    rw [← hfe]; exact fe.apply_symm_apply _
  have hsinj : Function.Injective s := by
    intro q q' h
    have h1 : (Quotient.out q : Lz) = Quotient.out q' := Subtype.ext (by rw [← hs_f, ← hs_f, h])
    rw [← Submodule.Quotient.mk_out q, ← Submodule.Quotient.mk_out q', h1]
  have key : ∀ z (hz : f z ∈ L) (q' : Lz ⧸ N),
      z - s q' ∈ L ↔ q' = Submodule.Quotient.mk (⟨f z, hz⟩ : Lz) := by
    intro z hz q'
    constructor
    · intro h
      have hm : (⟨f z, hz⟩ : Lz) - Quotient.out q' ∈ N :=
        ⟨⟨z - s q', h⟩, by ext; simp [fL, hs_f]⟩
      rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_out] at hm
      exact hm.symm
    · intro h
      have hm : (⟨f z, hz⟩ : Lz) - Quotient.out q' ∈ N := by
        rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_out, h]
      obtain ⟨l, hl⟩ := hm
      have : f (l : E) = f (z - s q') := by
        rw [← hfL, hl, map_sub, hs_f]; rfl
      rw [← finj this]; exact l.2
  refine ⟨Finset.univ.image s, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz
    rw [hs_f]; exact (Quotient.out q).2
  · intro z hz
    refine ⟨s (Submodule.Quotient.mk (⟨f z, hz⟩ : Lz)), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
      (key z hz _).mpr rfl⟩, ?_⟩
    rintro z' ⟨hz', hzz'⟩
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz'
    rw [(key z hz q).mp hzz']
  · rw [Finset.card_image_of_injective _ hsinj, Finset.card_univ, ← Nat.card_eq_fintype_card, ← hcard,
      ← hdetZ, Nat.cast_natAbs, Int.cast_abs]

/- English proof (translation)
Introduce `hDR W _ _ _ Λ hd hs Θ hΘ hdet`. Set `f : W →ₗ[ℝ] W` to `(1 - Θ).restrictScalars ℝ`. Establish `hR : ((LinearMap.det f : ℝ) : ℂ) = _` using `hDR W (1 - Θ)`. Establish `hdf : LinearMap.det f = Complex.normSq (LinearMap.det (1 - Θ))`. Apply `Complex.ofReal_injective` to reduce the goal to its premises.

Rewrite using `[hR, Complex.mul_conj]`. Establish `hfz : ∀ z, f z ∈ Λ ↔ Θ z - z ∈ Λ`. Introduce `z`. Use `show (1 - Θ) z ∈ Λ ↔ _`. Rewrite using `[LinearMap.sub_apply, Module.End.one_apply, ← neg_sub, neg_mem_iff]`.

Establish `hfL : ∀ z ∈ Λ, f z ∈ Λ` using `fun z hz => (hfz z).mpr (sub_mem (hΘ z hz) hz)`. Establish `hpos : 0 < LinearMap.det f` using `by rw [hdf]; exact Complex.normSq_pos.mpr hdet`. Take `⟨Fz, h1, h2, h3⟩` from `exists_lattice_reps Λ hd hs f hfL hpos.ne'`. Use `⟨Fz, fun z hz => (hfz z).mp (h1 z hz), fun z hz => h2 z ((hfz z).mpr hz), ?_⟩` and prove the remaining obligations. Rewrite using `[Complex.mul_conj, ← hdf, ← abs_of_pos hpos, ← h3]`.

Use `norm_cast`.
-/
theorem UpperTheory.Gal.W2.torusCount_of :
    UpperTheory.Gal.W2.DetReal → UpperTheory.Gal.W2.TorusCount := by
  intro hDR W _ _ _ Λ hd hs Θ hΘ hdet
  let f : W →ₗ[ℝ] W := (1 - Θ).restrictScalars ℝ
  have hR : ((LinearMap.det f : ℝ) : ℂ) = _ := hDR W (1 - Θ)
  have hdf : LinearMap.det f = Complex.normSq (LinearMap.det (1 - Θ)) := by
    apply Complex.ofReal_injective
    rw [hR, Complex.mul_conj]
  have hfz : ∀ z, f z ∈ Λ ↔ Θ z - z ∈ Λ := by
    intro z
    show (1 - Θ) z ∈ Λ ↔ _
    rw [LinearMap.sub_apply, Module.End.one_apply, ← neg_sub, neg_mem_iff]
  have hfL : ∀ z ∈ Λ, f z ∈ Λ := fun z hz => (hfz z).mpr (sub_mem (hΘ z hz) hz)
  have hpos : 0 < LinearMap.det f := by rw [hdf]; exact Complex.normSq_pos.mpr hdet
  obtain ⟨Fz, h1, h2, h3⟩ := exists_lattice_reps Λ hd hs f hfL hpos.ne'
  refine ⟨Fz, fun z hz => (hfz z).mp (h1 z hz), fun z hz => h2 z ((hfz z).mpr hz), ?_⟩
  rw [Complex.mul_conj, ← hdf, ← abs_of_pos hpos, ← h3]
  norm_cast
