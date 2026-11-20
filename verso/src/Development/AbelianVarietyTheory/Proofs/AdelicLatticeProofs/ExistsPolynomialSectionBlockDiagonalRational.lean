import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPolynomialSectionBlockDiagonalMapStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.PolySection

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def IsNatural (F : ∀ (R : Type) [CommRing R] [Algebra ℚ R], Matrix ι ι R → Matrix ι ι R) : Prop :=
  ∀ (R S : Type) [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S) (x : Matrix ι ι R),
    φ.mapMatrix (F R x) = F S (φ.mapMatrix x)

noncomputable def evHom {R : Type} [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R) :
    MvPolynomial (ι × ι) ℚ →ₐ[ℚ] R :=
  MvPolynomial.aeval (fun ij : ι × ι => y ij.1 ij.2)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[evHom, Matrix.mvPolynomialX]`.
-/
theorem evHom_generic {R : Type} [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R) :
    (evHom y).mapMatrix (Matrix.mvPolynomialX ι ι ℚ) = y := by
  ext i j
  simp [evHom, Matrix.mvPolynomialX]

/- English proof (translation)
Unfold `ev`. Rewrite using `[← AlgHom.comp_apply, MvPolynomial.comp_aeval]`. Both sides reduce to the same expression.
-/
theorem map_ev {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (f : MvPolynomial (ι × ι) ℚ) (x : Matrix ι ι R) : φ (ev f x) = ev f (φ.mapMatrix x) := by
  unfold ev
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Conclude with `φ.commutes _`.
-/
theorem map_rat {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (e : Matrix ι ι ℚ) : φ.mapMatrix (e.map (algebraMap ℚ R)) = e.map (algebraMap ℚ S) := by
  ext i j
  exact φ.commutes _

/- English proof (translation)
Simplify using `only [blk, map_add, map_mul, map_sub, map_one, map_rat]`.
-/
theorem map_blk {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (e : Matrix ι ι ℚ) (x : Matrix ι ι R) : φ.mapMatrix (blk e x) = blk e (φ.mapMatrix x) := by
  simp only [blk, map_add, map_mul, map_sub, map_one, map_rat]

/- English proof (translation)
Use extensionality with `i j`. Use `show φ (∑ kl : ι × ι, algebraMap ℚ R (c (i, j) kl) * x kl.1 kl.2) = ∑ kl : ι × ι, algebraMap ℚ S (c (i, j) kl) * φ (x kl.1 kl.2)`. Simplify using `only [map_sum, map_mul, AlgHom.commutes]`.
-/
theorem map_linExt {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (c : ι × ι → ι × ι → ℚ) (x : Matrix ι ι R) : φ.mapMatrix (linExt c x) = linExt c (φ.mapMatrix x) := by
  ext i j
  show φ (∑ kl : ι × ι, algebraMap ℚ R (c (i, j) kl) * x kl.1 kl.2) =
    ∑ kl : ι × ι, algebraMap ℚ S (c (i, j) kl) * φ (x kl.1 kl.2)
  simp only [map_sum, map_mul, AlgHom.commutes]

/- English proof (translation)
Use extensionality with `i j`. Conclude with `map_ev φ _ _`.
-/
theorem map_poly {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (b : ι → ι → MvPolynomial (ι × ι) ℚ) (x : Matrix ι ι R) :
    φ.mapMatrix (Matrix.of fun i j => ev (b i j) x) = Matrix.of fun i j => ev (b i j) (φ.mapMatrix x) := by
  ext i j
  exact map_ev φ _ _

/- English proof (translation)
Introduce `f hf`. Establish `key : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (z : Matrix ι ι S), ev (ev f (F _ (Matrix.mvPolynomialX ι ι ℚ))) z = ev f (F S z)`. Introduce `S _ _ z`. Use `map_ev (evHom z) f (F _ (Matrix.mvPolynomialX ι ι ℚ))` as an intermediate fact. Rewrite `this` using `[hF, evHom_generic]`.

Conclude with `this`. Rewrite using `[← key]`. Apply `hy` to reduce the goal to its premises. Introduce `g hg`. Rewrite using `[key]`.

Conclude with `hf _ (h g hg)`.
-/
theorem transfer_mem {F : ∀ (R : Type) [CommRing R] [Algebra ℚ R], Matrix ι ι R → Matrix ι ι R}
    (hF : IsNatural F) {Γ Γ' : Set (Matrix ι ι ℂ)} (h : ∀ g ∈ Γ, F ℂ g ∈ Γ')
    {R : Type} [CommRing R] [Algebra ℚ R] {y : Matrix ι ι R} (hy : y ∈ pts Γ R) : F R y ∈ pts Γ' R := by
  intro f hf
  have key : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (z : Matrix ι ι S),
      ev (ev f (F _ (Matrix.mvPolynomialX ι ι ℚ))) z = ev f (F S z) := by
    intro S _ _ z
    have := map_ev (evHom z) f (F _ (Matrix.mvPolynomialX ι ι ℚ))
    rw [hF, evHom_generic] at this
    exact this
  rw [← key]
  apply hy
  intro g hg
  rw [key]
  exact hf _ (h g hg)

/- English proof (translation)
Use extensionality with `i j`. Establish `key : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (z : Matrix ι ι S), ev (F _ (Matrix.mvPolynomialX ι ι ℚ) i j - G _ (Matrix.mvPolynomialX ι ι ℚ) i j) z = F S z i j - G S z i j`. Introduce `S _ _ z`. Establish `h1` using `hF _ _ (evHom z) (Matrix.mvPolynomialX ι ι ℚ)`. Establish `h2` using `hG _ _ (evHom z) (Matrix.mvPolynomialX ι ι ℚ)`.

Rewrite `h1`, `h2` using `[evHom_generic]`. Rewrite using `[← h1, ← h2]`. Conclude with `map_sub (evHom z) _ _`. Rewrite using `[← sub_eq_zero, ← key]`. Apply `hy` to reduce the goal to its premises.

Introduce `g hg`. Rewrite using `[key, h g hg, sub_self]`.
-/
theorem transfer_eq {F G : ∀ (R : Type) [CommRing R] [Algebra ℚ R], Matrix ι ι R → Matrix ι ι R}
    (hF : IsNatural F) (hG : IsNatural G) {Γ : Set (Matrix ι ι ℂ)} (h : ∀ g ∈ Γ, F ℂ g = G ℂ g)
    {R : Type} [CommRing R] [Algebra ℚ R] {y : Matrix ι ι R} (hy : y ∈ pts Γ R) : F R y = G R y := by
  ext i j
  have key : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (z : Matrix ι ι S),
      ev (F _ (Matrix.mvPolynomialX ι ι ℚ) i j - G _ (Matrix.mvPolynomialX ι ι ℚ) i j) z
        = F S z i j - G S z i j := by
    intro S _ _ z
    have h1 := hF _ _ (evHom z) (Matrix.mvPolynomialX ι ι ℚ)
    have h2 := hG _ _ (evHom z) (Matrix.mvPolynomialX ι ι ℚ)
    rw [evHom_generic] at h1 h2
    rw [← h1, ← h2]
    exact map_sub (evHom z) _ _
  rw [← sub_eq_zero, ← key]
  apply hy
  intro g hg
  rw [key, h g hg, sub_self]

/- English proof (translation)
Introduce `f hf`. Establish `h0 : MvPolynomial.map (algebraMap ℚ ℂ) f = 0`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Use `hf (Matrix.of fun i j => x (i, j)) (Set.mem_univ _)` as an intermediate fact.

Rewrite using `[map_zero, MvPolynomial.eval_map, ← MvPolynomial.aeval_def]`. Conclude with `this`. Establish `: f = 0` using `MvPolynomial.map_injective _ (algebraMap ℚ ℂ).injective (by rw [h0, map_zero])`. Substitute `this` using the available equality. Simplify using `[ev]`.
-/
theorem mem_pts_univ {R : Type} [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R) :
    y ∈ pts (Set.univ : Set (Matrix ι ι ℂ)) R := by
  intro f hf
  have h0 : MvPolynomial.map (algebraMap ℚ ℂ) f = 0 := by
    apply MvPolynomial.funext
    intro x
    have := hf (Matrix.of fun i j => x (i, j)) (Set.mem_univ _)
    rw [map_zero, MvPolynomial.eval_map, ← MvPolynomial.aeval_def]
    exact this
  have : f = 0 := MvPolynomial.map_injective _ (algebraMap ℚ ℂ).injective (by rw [h0, map_zero])
  subst this
  simp [ev]

/- English proof (translation)
Introduce `ι _ _ Γ e hΓ he htri`. Take `⟨c, b, hc, h1, hb⟩` from `GlobalTheory.T.exists_polynomial_section_blockDiagonal_map ι Γ e hΓ he htri`. Use `⟨c, b, fun R _ _ => ⟨fun X => ?_, fun X Y => ?_, fun y hy hy1 => ?_, fun x hx => ⟨?_, ?_⟩, fun y hy => ⟨?_, ?_⟩⟩⟩` and prove the remaining obligations. Establish `h` using `transfer_mem (F := fun R _ _ X => 1 + linExt c X) (fun R S _ _ _ _ φ x => by simp only [map_add, map_one, map_linExt]) (fun g _ => (hc g).1) (mem_pts_univ X)`. Conclude with `h`.

Establish `hp : ∀ X : Matrix ι ι R, e.map (algebraMap ℚ R) * linExt c X * (1 - e.map (algebraMap ℚ R)) = linExt c X` using `fun X => by`. Establish `h` using `transfer_eq (F := fun R _ _ X => e.map (algebraMap ℚ R) * linExt c X * (1 - e.map (algebraMap ℚ R))) (G := fun R _ _ X => linExt c X) (fun R S _ _ _ _ φ x => by simp only [map_mul, map_sub, map_one, map_linExt, map_rat]) (fun R S _ _ _ _ φ x => by simp only [map_linExt]) (by intr …`. Conclude with `h`. Establish `hE : (1 - e.map (algebraMap ℚ R)) * e.map (algebraMap ℚ R) = 0`. Rewrite using `[sub_mul, one_mul, ← Matrix.map_mul, he, sub_self]`.

Rewrite using `[← hp X, ← hp Y]`. Combine the equalities or inequalities in the displayed calculation. Establish `hone : (Matrix.of fun i j => ev (b i j) (1 : Matrix ι ι R)) = 1`. Establish `hq : (Matrix.of fun i j => ev (b i j) (1 : Matrix ι ι ℚ)) = 1`. Use `map_poly (Algebra.ofId ℚ ℂ) b 1` as an intermediate fact.

Rewrite `this` using `[map_one, h1]`. Use extensionality with `i j`. Apply `(algebraMap ℚ ℂ).injective` to reduce the goal to its premises. Establish `h2` using `congrFun (congrFun this i) j`. Rewrite `h2` using `[← map_one (Algebra.ofId ℚ ℂ).mapMatrix]`.

Conclude with `h2`. Use `map_poly (Algebra.ofId ℚ R) b 1` as an intermediate fact. Rewrite `this` using `[hq, map_one]`. Conclude with `this.symm`. Establish `h` using `transfer_eq (F := fun R _ _ g => g) (G := fun R _ _ g => (1 + linExt c (e.map (algebraMap ℚ R) * g * (1 - e.map (algebraMap ℚ R)) * (blk e g).adjugate)) * (Matrix.of fun i j => ev (b i j) (blk e g))) (fun R S _ _ _ _ φ x => rfl) (fun R S _ _ _ _ φ x => by`.

Simplify using `only [map_mul, map_add, map_sub, map_one, map_linExt, map_rat, map_poly, map_blk, AlgHom.map_adjugate])`. Use the proof step `(Γ := Γ) (by intro g hg; beta_reduce; exact (hb g hg).2.2) hy`. Simplify using `only [hy1, hone, mul_one] at h`. Conclude with `⟨_, h⟩`. Establish `h` using `transfer_eq (F := fun R _ _ x => (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R)) (G := fun R _ _ _ => 0) (fun R S _ _ _ _ φ x => by simp only [map_mul, map_sub, map_one, map_rat]) (fun R S _ _ _ _ φ x => by simp only [map_zero]) (by intro g hg; beta_reduce; exact htri …`.

Conclude with `h`. Establish `h` using `transfer_mem (F := fun R _ _ x => blk e x) (fun R S _ _ _ _ φ x => map_blk φ e x) (Γ' := blk e '' Γ) (fun g hg => ⟨g, hg, rfl⟩) hx`. Conclude with `h`. Establish `h` using `transfer_mem (F := fun R _ _ x => Matrix.of fun i j => ev (b i j) x) (fun R S _ _ _ _ φ x => map_poly φ b x) (Γ' := Γ) (by rintro _ ⟨g, hg, rfl⟩; beta_reduce; exact (hb g hg).1) hy`. Conclude with `h`.

Establish `h` using `transfer_eq (F := fun R _ _ x => blk e (Matrix.of fun i j => ev (b i j) x)) (G := fun R _ _ x => x) (fun R S _ _ _ _ φ x => by simp only [map_blk, map_poly]) (fun R S _ _ _ _ φ x => rfl) (by rintro _ ⟨g, hg, rfl⟩; beta_reduce; exact (hb g hg).2.1) hy`. Conclude with `h`.
-/
theorem exists_section : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∃ (c : ι × ι → ι × ι → ℚ) (b : ι → ι → MvPolynomial (ι × ι) ℚ), ∀ (R : Type) [CommRing R] [Algebra ℚ R], (∀ X : Matrix ι ι R, 1 + linExt c X ∈ pts Γ R) ∧ (∀ X Y : Matrix ι ι R, linExt c X * linExt c Y = 0) ∧ (∀ y ∈ pts Γ R, blk e y = 1 → ∃ X : Matrix ι ι R, y = 1 + linExt c X) ∧ (∀ x ∈ pts Γ R, (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R) = 0 ∧ blk e x ∈ pts (blk e '' Γ) R) ∧ ∀ y ∈ pts (blk e '' Γ) R, (Matrix.of fun i j => ev (b i j) (y)) ∈ pts Γ R ∧ blk e (Matrix.of fun i j => ev (b i j) (y)) = y := by
  intro ι _ _ Γ e hΓ he htri
  obtain ⟨c, b, hc, h1, hb⟩ := GlobalTheory.T.exists_polynomial_section_blockDiagonal_map ι Γ e hΓ he htri
  refine ⟨c, b, fun R _ _ => ⟨fun X => ?_, fun X Y => ?_, fun y hy hy1 => ?_, fun x hx => ⟨?_, ?_⟩,
    fun y hy => ⟨?_, ?_⟩⟩⟩
  · have h := transfer_mem (F := fun R _ _ X => 1 + linExt c X)
      (fun R S _ _ _ _ φ x => by simp only [map_add, map_one, map_linExt])
      (fun g _ => (hc g).1) (mem_pts_univ X)
    exact h
  · have hp : ∀ X : Matrix ι ι R,
        e.map (algebraMap ℚ R) * linExt c X * (1 - e.map (algebraMap ℚ R)) = linExt c X := fun X => by
      have h := transfer_eq (F := fun R _ _ X => e.map (algebraMap ℚ R) * linExt c X * (1 - e.map (algebraMap ℚ R)))
        (G := fun R _ _ X => linExt c X)
        (fun R S _ _ _ _ φ x => by simp only [map_mul, map_sub, map_one, map_linExt, map_rat])
        (fun R S _ _ _ _ φ x => by simp only [map_linExt])
        (by intro g _; beta_reduce; exact (hc g).2) (mem_pts_univ X)
      exact h
    have hE : (1 - e.map (algebraMap ℚ R)) * e.map (algebraMap ℚ R) = 0 := by
      rw [sub_mul, one_mul, ← Matrix.map_mul, he, sub_self]
    rw [← hp X, ← hp Y]
    calc _ = e.map (algebraMap ℚ R) * linExt c X * ((1 - e.map (algebraMap ℚ R)) * e.map (algebraMap ℚ R)) *
          linExt c Y * (1 - e.map (algebraMap ℚ R)) := by simp only [mul_assoc]
      _ = 0 := by rw [hE]; simp
  · have hone : (Matrix.of fun i j => ev (b i j) (1 : Matrix ι ι R)) = 1 := by
      have hq : (Matrix.of fun i j => ev (b i j) (1 : Matrix ι ι ℚ)) = 1 := by
        have := map_poly (Algebra.ofId ℚ ℂ) b 1
        rw [map_one, h1] at this
        ext i j
        apply (algebraMap ℚ ℂ).injective
        have h2 := congrFun (congrFun this i) j
        rw [← map_one (Algebra.ofId ℚ ℂ).mapMatrix] at h2
        exact h2
      have := map_poly (Algebra.ofId ℚ R) b 1
      rw [hq, map_one] at this
      exact this.symm
    have h := transfer_eq (F := fun R _ _ g => g)
      (G := fun R _ _ g => (1 + linExt c (e.map (algebraMap ℚ R) * g * (1 - e.map (algebraMap ℚ R)) *
        (blk e g).adjugate)) * (Matrix.of fun i j => ev (b i j) (blk e g)))
      (fun R S _ _ _ _ φ x => rfl)
      (fun R S _ _ _ _ φ x => by
        simp only [map_mul, map_add, map_sub, map_one, map_linExt, map_rat, map_poly, map_blk,
          AlgHom.map_adjugate])
      (Γ := Γ) (by intro g hg; beta_reduce; exact (hb g hg).2.2) hy
    simp only [hy1, hone, mul_one] at h
    exact ⟨_, h⟩
  · have h := transfer_eq (F := fun R _ _ x => (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R))
      (G := fun R _ _ _ => 0)
      (fun R S _ _ _ _ φ x => by simp only [map_mul, map_sub, map_one, map_rat])
      (fun R S _ _ _ _ φ x => by simp only [map_zero])
      (by intro g hg; beta_reduce; exact htri g hg) hx
    exact h
  · have h := transfer_mem (F := fun R _ _ x => blk e x) (fun R S _ _ _ _ φ x => map_blk φ e x)
      (Γ' := blk e '' Γ) (fun g hg => ⟨g, hg, rfl⟩) hx
    exact h
  · have h := transfer_mem (F := fun R _ _ x => Matrix.of fun i j => ev (b i j) x)
      (fun R S _ _ _ _ φ x => map_poly φ b x)
      (Γ' := Γ) (by rintro _ ⟨g, hg, rfl⟩; beta_reduce; exact (hb g hg).1) hy
    exact h
  · have h := transfer_eq (F := fun R _ _ x => blk e (Matrix.of fun i j => ev (b i j) x))
      (G := fun R _ _ x => x)
      (fun R S _ _ _ _ φ x => by simp only [map_blk, map_poly])
      (fun R S _ _ _ _ φ x => rfl)
      (by rintro _ ⟨g, hg, rfl⟩; beta_reduce; exact (hb g hg).2.1) hy
    exact h

end GlobalTheory.ClassFin.PolySection
