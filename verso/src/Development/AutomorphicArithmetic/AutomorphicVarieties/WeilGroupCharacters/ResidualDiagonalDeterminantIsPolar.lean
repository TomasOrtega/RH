import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocConstOfKer

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W Polynomial

namespace UpperTheory.V.W

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.LocallyConstantOfKernelCapelliIdentities.locConst_of_ker χ h`.
-/
private theorem locConst_of_ker {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    (χ : G →* M) (h : IsOpen (χ.ker : Set G)) : IsLocallyConstant χ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernelCapelliIdentities.locConst_of_ker χ h

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Use `Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (h i) x` as an intermediate fact. Conclude with `this.mono fun y hy => funext hy`.
-/
private theorem locConst_pi {G M ι : Type} [TopologicalSpace G] [Finite ι] (f : ι → G → M)
    (h : ∀ i, IsLocallyConstant (f i)) : IsLocallyConstant fun g i => f i g := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have := Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (h i) x
  exact this.mono fun y hy => funext hy

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(GDet.repAlg ρ A[X] _).det = _`. Rewrite using `[map_sub]`. Use `congr 2`. Use extensionality with `i j : 2`. Apply the tactic sequence `by_cases h : i = j <;> simp [GDet.repAlg, Matrix.one_apply, Matrix.diagonal_apply, h]`.
-/
private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (y : MonoidAlgebra A G) : (GDet.ofRep ρ).chi y =
      (Matrix.scalar (Fin n) X - GDet.repAlg ρ A[X] (MonoidAlgebra.mapRingHom G C y)).det := by
  change (GDet.repAlg ρ A[X] _).det = _
  rw [map_sub]
  congr 2
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.one_apply, Matrix.diagonal_apply, h]

/- English proof (translation)
Simplify using `[GFrame.star, GFrame.starOp]`.
-/
private theorem star_single {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (b : R) :
    F.star O R n (MonoidAlgebra.single g b) =
      MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp [GFrame.star, GFrame.starOp]

/- English proof (translation)
Simplify using `[GFrame.star]`.
-/
private theorem star_sub {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (x y : MonoidAlgebra R F.G₀) :
    F.star O R n (x - y) = F.star O R n x - F.star O R n y := by
  simp [GFrame.star]

/- English proof (translation)
Establish `h : F.eps O R[X] g = Units.map (C : R →+* R[X]).toMonoidHom (F.eps O R g)` using `Units.ext rfl`. Rewrite using `[h, ← map_zpow]`. Both sides reduce to the same expression.
-/
private theorem eps_C {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) (m : ℤ) :
    ((F.eps O R[X] g ^ m : R[X]ˣ) : R[X]) = C ((F.eps O R g ^ m : Rˣ) : R) := by
  have h : F.eps O R[X] g = Units.map (C : R →+* R[X]).toMonoidHom (F.eps O R g) := Units.ext rfl
  rw [h, ← map_zpow]
  rfl

end UpperTheory.V.W

/- English proof (translation)
Introduce `l _ F O _ _ _ _ _ _ _ n r _ hn hok`. Establish `hres : ∀ x, res O (ResidueField O) x = x` using `fun x => by`. Take `⟨a, rfl⟩` from `residue_surjective x`. Conclude with `(res O (ResidueField O)).commutes a`. Establish `hres' : (res O (ResidueField O) : ResidueField O →+* ResidueField O) = RingHom.id _` using `RingHom.ext hres`.

Use `⟨⟨r.Dbar, r.psib, fun i N => ?_, ?_, fun v i => ⟨fun N => ?_, fun g => hres _, fun g => ?_⟩, fun i g => ?_, hok.1, fun u g hg h => ?_⟩, rfl, rfl⟩` and prove the remaining obligations. Establish `h1` using `locConst_pi _ fun j => locConst_of_ker _ (r.chib_open j)`. Use `(IsLocallyConstant.iff_eventually_eq _).2 fun x => ((IsLocallyConstant.iff_eventually_eq _).1 h1 x).mono fun y hy => ?_` and prove the remaining obligations. Establish `h2 : diagRep r.chib y = diagRep r.chib x`. Express the relevant statement in the definitionally equal form `Matrix.diagonal _ = Matrix.diagonal _`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[congrFun hy j]`. Simplify using `only [Resid.Dbar, GDet.lam, chi_ofRep]`. Simplify using `[GDet.repAlg, h2]`.

Rewrite using `[hres']`. Both sides reduce to the same expression. Conclude with `(locConst_of_ker _ (r.psib_open v i)).comp fun u => Ideal.Quotient.mk _ (u : ResidueField O)`. Rewrite using `[hok.2 v i g]`. Both sides reduce to the same expression.

Establish `h1` using `r.polar (ResidueField O)[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom _ C (MonoidAlgebra.single g (1 : ResidueField O)))`. Simplify using `only [GDet.lam, GDet.chi, Resid.Dbar]`. Rewrite using `[← h1, star_sub]`. Simplify using `only [MonoidAlgebra.mapRingHom_single, star_single, eps_C]`. Simplify using the standard rewrite rules.

Establish `h2 : diagRep r.chib g = 1`. Express the relevant statement in the definitionally equal form `Matrix.diagonal _ = Matrix.diagonal _`. Use `congr 1`. Use function extensionality and compare the values at `j`. Establish `h3 : r.chib j g = 1` using `(Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hg).2) j`.

Rewrite using `[h3]`. Both sides reduce to the same expression. Establish `h4 : GDet.repAlg (diagRep r.chib) (ResidueField O)[X] (MonoidAlgebra.mapRingHom _ C (MonoidAlgebra.single h (1 : ResidueField O) * (MonoidAlgebra.single g 1 - 1))) = 0`. Rewrite using `[map_mul, map_mul, map_sub, map_sub, map_one, map_one]`. Simplify using `[GDet.repAlg, h2]`.

Simplify using `only [GDet.tr, Resid.Dbar, GDet.lam, chi_ofRep, h4, sub_zero]`. Establish `h5 : n - 1 ≠ n` using `by omega`. Simplify using `[Matrix.scalar_apply, coeff_X_pow, h5]`.
-/
theorem UpperTheory.V.W.residual_diagonal_determinant_isPolar :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (n : ℕ) (r : Resid F O n) [IsCO O (ResidueField O)], 1 ≤ n → r.Ok → ∃ p : Pair r (ResidueField O), p.D = r.Dbar ∧ p.ψ = r.psib := by
  intro l _ F O _ _ _ _ _ _ _ n r _ hn hok
  have hres : ∀ x, res O (ResidueField O) x = x := fun x => by
    obtain ⟨a, rfl⟩ := residue_surjective x
    exact (res O (ResidueField O)).commutes a
  have hres' : (res O (ResidueField O) : ResidueField O →+* ResidueField O) = RingHom.id _ := RingHom.ext hres
  refine ⟨⟨r.Dbar, r.psib, fun i N => ?_, ?_, fun v i => ⟨fun N => ?_, fun g => hres _, fun g => ?_⟩, fun i g => ?_,
    hok.1, fun u g hg h => ?_⟩, rfl, rfl⟩
  · have h1 := locConst_pi _ fun j => locConst_of_ker _ (r.chib_open j)
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ((IsLocallyConstant.iff_eventually_eq _).1 h1 x).mono fun y hy => ?_
    have h2 : diagRep r.chib y = diagRep r.chib x := by
      change Matrix.diagonal _ = Matrix.diagonal _
      congr 1
      funext j
      rw [congrFun hy j]
    simp only [Resid.Dbar, GDet.lam, chi_ofRep]
    simp [GDet.repAlg, h2]
  · rw [hres']
    rfl
  · exact (locConst_of_ker _ (r.psib_open v i)).comp fun u => Ideal.Quotient.mk _ (u : ResidueField O)
  · rw [hok.2 v i g]
    rfl
  · have h1 := r.polar (ResidueField O)[X] (MonoidAlgebra.single 1 X -
      MonoidAlgebra.mapRingHom _ C (MonoidAlgebra.single g (1 : ResidueField O)))
    simp only [GDet.lam, GDet.chi, Resid.Dbar]
    rw [← h1, star_sub]
    simp only [MonoidAlgebra.mapRingHom_single, star_single, eps_C]
    simp
  · have h2 : diagRep r.chib g = 1 := by
      change Matrix.diagonal _ = Matrix.diagonal _
      congr 1
      funext j
      have h3 : r.chib j g = 1 := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hg).2) j
      rw [h3]
      rfl
    have h4 : GDet.repAlg (diagRep r.chib) (ResidueField O)[X] (MonoidAlgebra.mapRingHom _ C
        (MonoidAlgebra.single h (1 : ResidueField O) * (MonoidAlgebra.single g 1 - 1))) = 0 := by
      rw [map_mul, map_mul, map_sub, map_sub, map_one, map_one]
      simp [GDet.repAlg, h2]
    simp only [GDet.tr, Resid.Dbar, GDet.lam, chi_ofRep, h4, sub_zero]
    have h5 : n - 1 ≠ n := by omega
    simp [Matrix.scalar_apply, coeff_X_pow, h5]
