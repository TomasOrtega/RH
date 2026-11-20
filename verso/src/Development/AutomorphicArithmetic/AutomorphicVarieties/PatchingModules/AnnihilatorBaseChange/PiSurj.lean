import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpoCo

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

/- English proof (translation)
Rewrite using `[← res_eq_zero_iff O, res_map, res_eq_zero_iff]`.
-/
private theorem mem_iff {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (y : R) :
    f y ∈ maximalIdeal R' ↔ y ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

/- English proof (translation)
Establish `hmB : ∀ y : B, algebraMap B C y ∈ maximalIdeal C ↔ y ∈ maximalIdeal B` using `fun y => by`. Simplify using `using mem_iff (IsScalarTower.toAlgHom O B C) y`. Establish `hpow : ∀ N (y : B), y ∈ maximalIdeal B ^ N → algebraMap B C y ∈ maximalIdeal C ^ N`. Introduce `N y hy`. Establish `hle : Ideal.map (algebraMap B C) (maximalIdeal B) ≤ maximalIdeal C`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `z hz`. Conclude with `(hmB z).2 hz`. Establish `h1' : algebraMap B C y ∈ Ideal.map (algebraMap B C) (maximalIdeal B ^ N)` using `Ideal.mem_map_of_mem _ hy`. Rewrite `h1'` using `[Ideal.map_pow]`.

Conclude with `Ideal.pow_right_mono hle N h1'`. Establish `hadj : Algebra.adjoin O S ≤ (f.range).comap (IsScalarTower.toAlgHom O B C)`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce `b hb`. Simplify using `using h1 b hb`.

Set `P : Subalgebra B C` to `{ carrier := {c | ∀ N, ∃ r, c - f r ∈ maximalIdeal C ^ N} mul_mem' := by`. Introduce `a b ha hb N`. Take `⟨r1, hr1⟩` from `ha N`. Take `⟨r2, hr2⟩` from `hb N`. Use `⟨r1 * r2, ?_⟩` and prove the remaining obligations.

Establish `e : a * b - f (r1 * r2) = (a - f r1) * b + f r1 * (b - f r2)`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ hr1) (Ideal.mul_mem_left _ _ hr2)`.

Use the proof step `add_mem' := by`. Introduce `a b ha hb N`. Take `⟨r1, hr1⟩` from `ha N`. Take `⟨r2, hr2⟩` from `hb N`. Use `⟨r1 + r2, ?_⟩` and prove the remaining obligations.

Establish `e : a + b - f (r1 + r2) = (a - f r1) + (b - f r2)`. Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ hr1 hr2`.

Use the proof step `algebraMap_mem' := by`. Introduce `b N`. Take `⟨a, ha, hba⟩` from `hS N b`. Establish `ha'` using `hadj ha`. Rewrite `ha'` using `[Subalgebra.mem_comap, AlgHom.mem_range]`.

Take `⟨r, hr⟩` from `ha'`. Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `hr' : f r = algebraMap B C a` using `by simpa using hr`. Rewrite using `[hr', ← map_sub]`. Conclude with `hpow N _ hba }`.

Establish `hUP : Algebra.adjoin B U ≤ P`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce `c hc N`. Take `⟨r, hr⟩` from `(AlgHom.mem_range f).1 (h2 c hc)`. Conclude with `⟨r, by rw [hr, sub_self]; exact Ideal.zero_mem _⟩`.

Establish `hall : ∀ c : C, ∀ N, ∃ r, c - f r ∈ maximalIdeal C ^ N`. Introduce `c`. Establish `hc : c ∈ Algebra.adjoin B U`. Rewrite using `[hU]`. Conclude with `Algebra.mem_top`.

Conclude with `hUP hc`. Apply `co_surj O R C f` to reduce the goal to its premises. Introduce `m hm`. Take `⟨r, hr⟩` from `hall m 2`. Establish `hfr : f r ∈ maximalIdeal C`.

Establish `e : m - (m - f r) = f r` using `by ring`. Rewrite using `[← e]`. Conclude with `Ideal.sub_mem _ hm (Ideal.pow_le_self two_ne_zero hr)`. Establish `hrm : r ∈ maximalIdeal R` using `(mem_iff f r).1 hfr`. Establish `e : m = f r + (m - f r)` using `by ring`.

Rewrite using `[e]`. Conclude with `Submodule.add_mem_sup (Ideal.mem_map_of_mem f hrm) hr`.
-/
private theorem surj_of_gen {O : Type} [CommRing O] [IsLocalRing O] {R B C : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing B] [Algebra O B] [IsCO O B] [CommRing C] [Algebra O C] [IsCO O C] [Algebra B C] [IsScalarTower O B C]
    (f : R →ₐ[O] C) (S : Set B) (U : Set C) (hS : GenBy O S) (hU : Algebra.adjoin B U = ⊤)
    (h1 : ∀ b ∈ S, algebraMap B C b ∈ f.range) (h2 : ∀ c ∈ U, c ∈ f.range) : Function.Surjective f := by
  have hmB : ∀ y : B, algebraMap B C y ∈ maximalIdeal C ↔ y ∈ maximalIdeal B := fun y => by
    simpa using mem_iff (IsScalarTower.toAlgHom O B C) y
  have hpow : ∀ N (y : B), y ∈ maximalIdeal B ^ N → algebraMap B C y ∈ maximalIdeal C ^ N := by
    intro N y hy
    have hle : Ideal.map (algebraMap B C) (maximalIdeal B) ≤ maximalIdeal C := by
      rw [Ideal.map_le_iff_le_comap]
      intro z hz
      exact (hmB z).2 hz
    have h1' : algebraMap B C y ∈ Ideal.map (algebraMap B C) (maximalIdeal B ^ N) :=
      Ideal.mem_map_of_mem _ hy
    rw [Ideal.map_pow] at h1'
    exact Ideal.pow_right_mono hle N h1'
  have hadj : Algebra.adjoin O S ≤ (f.range).comap (IsScalarTower.toAlgHom O B C) := by
    rw [Algebra.adjoin_le_iff]
    intro b hb
    simpa using h1 b hb
  let P : Subalgebra B C :=
    { carrier := {c | ∀ N, ∃ r, c - f r ∈ maximalIdeal C ^ N}
      mul_mem' := by
        intro a b ha hb N
        obtain ⟨r1, hr1⟩ := ha N
        obtain ⟨r2, hr2⟩ := hb N
        refine ⟨r1 * r2, ?_⟩
        have e : a * b - f (r1 * r2) = (a - f r1) * b + f r1 * (b - f r2) := by
          rw [map_mul]
          ring
        rw [e]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hr1) (Ideal.mul_mem_left _ _ hr2)
      add_mem' := by
        intro a b ha hb N
        obtain ⟨r1, hr1⟩ := ha N
        obtain ⟨r2, hr2⟩ := hb N
        refine ⟨r1 + r2, ?_⟩
        have e : a + b - f (r1 + r2) = (a - f r1) + (b - f r2) := by
          rw [map_add]
          ring
        rw [e]
        exact Ideal.add_mem _ hr1 hr2
      algebraMap_mem' := by
        intro b N
        obtain ⟨a, ha, hba⟩ := hS N b
        have ha' := hadj ha
        rw [Subalgebra.mem_comap, AlgHom.mem_range] at ha'
        obtain ⟨r, hr⟩ := ha'
        refine ⟨r, ?_⟩
        have hr' : f r = algebraMap B C a := by simpa using hr
        rw [hr', ← map_sub]
        exact hpow N _ hba }
  have hUP : Algebra.adjoin B U ≤ P := by
    rw [Algebra.adjoin_le_iff]
    intro c hc N
    obtain ⟨r, hr⟩ := (AlgHom.mem_range f).1 (h2 c hc)
    exact ⟨r, by rw [hr, sub_self]; exact Ideal.zero_mem _⟩
  have hall : ∀ c : C, ∀ N, ∃ r, c - f r ∈ maximalIdeal C ^ N := by
    intro c
    have hc : c ∈ Algebra.adjoin B U := by
      rw [hU]
      exact Algebra.mem_top
    exact hUP hc
  apply co_surj O R C f
  intro m hm
  obtain ⟨r, hr⟩ := hall m 2
  have hfr : f r ∈ maximalIdeal C := by
    have e : m - (m - f r) = f r := by ring
    rw [← e]
    exact Ideal.sub_mem _ hm (Ideal.pow_le_self two_ne_zero hr)
  have hrm : r ∈ maximalIdeal R := (mem_iff f r).1 hfr
  have e : m = f r + (m - f r) := by ring
  rw [e]
  exact Submodule.add_mem_sup (Ideal.mem_map_of_mem f hrm) hr

/- English proof (translation)
Establish `e : (MonoidAlgebra.mapDomainRingHom (Polynomial A) φ) (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom H Polynomial.C) (MonoidAlgebra.single g 1)) = MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom G Polynomial.C) (MonoidAlgebra.single (φ g) 1)`. Rewrite using `[map_sub]`. Simplify using `[MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]`. Simplify using `only [GDet.lam, GDet.chi, GDet.comap, MonoidHom.coe_comp, Function.comp_apply]`. Conclude with `congrArg (fun y => (-1) ^ i * ((D.D (Polynomial A)) y).coeff (n - i)) e`.
-/
private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  have e : (MonoidAlgebra.mapDomainRingHom (Polynomial A) φ)
      (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom H Polynomial.C) (MonoidAlgebra.single g 1))
      = MonoidAlgebra.single 1 Polynomial.X
        - (MonoidAlgebra.mapRingHom G Polynomial.C) (MonoidAlgebra.single (φ g) 1) := by
    rw [map_sub]
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  simp only [GDet.lam, GDet.chi, GDet.comap, MonoidHom.coe_comp, Function.comp_apply]
  exact congrArg (fun y => (-1) ^ i * ((D.D (Polynomial A)) y).coeff (n - i)) e

/- English proof (translation)
Use `((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 i` as an intermediate fact. Rewrite `this` using `[MonoidAlgebra.mapRingHom_single, map_one]`. Then use the resulting hypothesis.
-/
private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B)
    (i : ℕ) (g : G) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 i
  rwa [MonoidAlgebra.mapRingHom_single, map_one] at this

/- English proof (translation)
Introduce `l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hAd hgen`. Use `letI := W.ring`. Use `letI := W.alg`. Use `haveI := W.co`. Take `⟨⟨hco, -, -, hadj⟩, -⟩` from `spoCo l L G0 T Λ n O r B u J D A hAd`.

Use `haveI := hco`. Take `⟨hD, hψ, -, hU, -⟩` from `m.π_maps`. Establish `hsurj : Function.Surjective (Λ.h.p₀.comp (πo0 Λ))` using `(Glob.Hom.p₀_surj Λ.h).comp (Lim.πo0_surj Λ)`. Use `surj_of_gen (O := O) m.π _ _ hgen hadj ?_ ?_` and prove the remaining obligations. Introduce `b hb`.

Break down `hb with (⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩) | hb` into its components or cases. Take `⟨h, rfl⟩` from `hsurj g`. Use `(AlgHom.mem_range _).2 ⟨W.t.D.lam i (MonoidAlgebra.single h 1), ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (fun E => E.lam i (MonoidAlgebra.single h 1)) hD`. Simplify using `only [lam_map, lam_comap] at e`.

Conclude with `e`. Use `(AlgHom.mem_range _).2 ⟨↑(W.t.ψ v i g), ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (fun χ => ((χ g : (Spo A)ˣ) : Spo A)) (hψ v i)`. Simplify using `using e`. Rewrite `hb` using `[Set.mem_singleton_iff]`.

Substitute `hb` using the available equality. Use `(AlgHom.mem_range _).2 ⟨m.s (MvPowerSeries.C (MvPowerSeries.X (Sum.inl ()))), ?_⟩` and prove the remaining obligations. Rewrite using `[m.π_s]`. Simplify using the standard rewrite rules. Introduce and unpack `c ⟨p, rfl⟩`.

Conclude with `(AlgHom.mem_range _).2 ⟨W.t.U p.1 p.2, hU p.1 p.2⟩`.
-/
theorem UpperTheory.V.Pa.Core.piSurj :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → GenBy O (pairVals u ∪ {(A.b.lam (MvPowerSeries.X (.inl ())))}) → Function.Surjective m.π := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hAd hgen
  letI := W.ring
  letI := W.alg
  haveI := W.co
  obtain ⟨⟨hco, -, -, hadj⟩, -⟩ := spoCo l L G0 T Λ n O r B u J D A hAd
  haveI := hco
  obtain ⟨hD, hψ, -, hU, -⟩ := m.π_maps
  have hsurj : Function.Surjective (Λ.h.p₀.comp (πo0 Λ)) :=
    (Glob.Hom.p₀_surj Λ.h).comp (Lim.πo0_surj Λ)
  refine surj_of_gen (O := O) m.π _ _ hgen hadj ?_ ?_
  · intro b hb
    rcases hb with (⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩) | hb
    · obtain ⟨h, rfl⟩ := hsurj g
      refine (AlgHom.mem_range _).2 ⟨W.t.D.lam i (MonoidAlgebra.single h 1), ?_⟩
      have e := congrArg (fun E => E.lam i (MonoidAlgebra.single h 1)) hD
      simp only [lam_map, lam_comap] at e
      exact e
    · refine (AlgHom.mem_range _).2 ⟨↑(W.t.ψ v i g), ?_⟩
      have e := congrArg (fun χ => ((χ g : (Spo A)ˣ) : Spo A)) (hψ v i)
      simpa using e
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      refine (AlgHom.mem_range _).2 ⟨m.s (MvPowerSeries.C (MvPowerSeries.X (Sum.inl ()))), ?_⟩
      rw [m.π_s]
      simp
  · rintro c ⟨p, rfl⟩
    exact (AlgHom.mem_range _).2 ⟨W.t.U p.1 p.2, hU p.1 p.2⟩
