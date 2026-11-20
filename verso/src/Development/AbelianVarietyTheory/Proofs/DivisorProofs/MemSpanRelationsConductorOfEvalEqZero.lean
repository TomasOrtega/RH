import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchKernel

/- English proof (translation)
Use `set J : Ideal (MvPolynomial ν R') := Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔ (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') with hJ`. Set `mkJ : MvPolynomial ν R' →+* MvPolynomial ν R' ⧸ J` to `Ideal.Quotient.mk J`. Establish `hc : ∀ r ∈ c, (mkJ.comp ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp a)) r = 0`. Introduce `r hr`. Simplify using `only [RingHom.comp_apply, mkJ]`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr))`. Set `base : R ⧸ c →+* MvPolynomial ν R' ⧸ J` to `Ideal.Quotient.lift c (mkJ.comp ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp a)) hc`. Set `φ : MvPolynomial ν (R ⧸ c) →+* MvPolynomial ν R' ⧸ J` to `MvPolynomial.eval₂Hom base (fun s ↦ mkJ (MvPolynomial.X s))`. Establish `hφC : ∀ r : R, φ (MvPolynomial.C (Ideal.Quotient.mk c r)) = mkJ (MvPolynomial.C (a r))`.

Introduce `r`. Simplify using `[φ, base]`. Establish `hφmap : ∀ P : MvPolynomial ν R, φ (MvPolynomial.map (Ideal.Quotient.mk c) P) = mkJ (MvPolynomial.map a P)`. Introduce `P`. Establish `h : φ.comp (MvPolynomial.map (Ideal.Quotient.mk c)) = mkJ.comp (MvPolynomial.map a)`.

Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `only [RingHom.comp_apply, MvPolynomial.map_C]`. Conclude with `hφC r`. Introduce `s`.

Simplify using `[φ]`. Conclude with `RingHom.congr_fun h P`. Set `q : MvPolynomial ν (R ⧸ c) →+* D` to `(MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D)`. Establish `hkerφ : RingHom.ker q ≤ RingHom.ker φ`. Establish `hq : RingHom.ker q = Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s))`.

Rewrite using `[← hker]`. Both sides reduce to the same expression. Rewrite using `[hq, Ideal.span_le]`. Introduce and unpack `_ ⟨s, rfl⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, hφmap, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.mem_sup_left (Ideal.subset_span ⟨s, rfl⟩)`. Set `dA : D →+* MvPolynomial ν R' ⧸ J` to `q.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨φ, hkerφ⟩`. Establish `hdA : ∀ p, dA (q p) = φ p` using `fun p => RingHom.liftOfRightInverse_comp_apply q _ _ ⟨φ, hkerφ⟩ p`. Establish `hqX : ∀ s, q (MvPolynomial.X s) = ζ s` using `fun s => by simp [q]`. Establish `hqC : ∀ x : R ⧸ c, q (MvPolynomial.C x) = algebraMap (R ⧸ c) D x` using `fun x => by`.

Simplify using `[q]`. Establish `w : CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) ≫ CommRingCat.ofHom dA = CommRingCat.ofHom a ≫ CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))`. Use extensionality with `r`. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]`. Rewrite using `[← hqC, hdA, hφC]`.

Set `desc` to `hpo.desc (CommRingCat.ofHom dA) (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w`. Establish `hinl : ∀ x : D, desc.hom (ψ x) = dA x` using `fun x => by`. Use `congrArg (fun f => f.hom x) (hpo.inl_desc (CommRingCat.ofHom dA) (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w)` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this`. Conclude with `this`.

Establish `hinr : ∀ x : R', desc.hom (χ x) = mkJ (MvPolynomial.C x)` using `fun x => by`. Use `congrArg (fun f => f.hom x) (hpo.inr_desc (CommRingCat.ofHom dA) (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w)` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this`. Conclude with `this`. Establish `hΦ : desc.hom.comp (MvPolynomial.eval₂Hom χ (fun s ↦ ψ (ζ s))) = mkJ`.

Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]`. Conclude with `hinr x`. Introduce `s`.

Simplify using `only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']`. Rewrite using `[hinl, ← hqX, hdA]`. Simplify using `[φ]`. Establish `h0 : mkJ G = 0`. Rewrite using `[← hΦ, RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, hG, map_zero]`.

Conclude with `(Ideal.Quotient.eq_zero_iff_mem).1 h0`.
-/
theorem mem_span_of_eval_eq_zero (R R' D E ν σ : Type) [CommRing R] [CommRing R'] [CommRing D] [CommRing E]
    (a : R →+* R') (c : Ideal R) [Algebra (R ⧸ c) D] (χ : R' →+* E) (ψ : D →+* E) (ζ : ν → D)
    (F : σ → MvPolynomial ν R)
    (hsurj : Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D))
    (hker : RingHom.ker (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) =
      Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)))
    (hpo : IsPushout (CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)))
      (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom χ))
    (G : MvPolynomial ν R') (hG : MvPolynomial.eval₂ χ (fun s ↦ ψ (ζ s)) G = 0) :
    G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔
      (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') := by
  classical
  set J : Ideal (MvPolynomial ν R') := Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔
      (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') with hJ
  let mkJ : MvPolynomial ν R' →+* MvPolynomial ν R' ⧸ J := Ideal.Quotient.mk J
  have hc : ∀ r ∈ c, (mkJ.comp ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp a)) r = 0 := by
    intro r hr
    simp only [RingHom.comp_apply, mkJ]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr))
  let base : R ⧸ c →+* MvPolynomial ν R' ⧸ J :=
    Ideal.Quotient.lift c (mkJ.comp ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp a)) hc
  let φ : MvPolynomial ν (R ⧸ c) →+* MvPolynomial ν R' ⧸ J :=
    MvPolynomial.eval₂Hom base (fun s ↦ mkJ (MvPolynomial.X s))
  have hφC : ∀ r : R, φ (MvPolynomial.C (Ideal.Quotient.mk c r)) = mkJ (MvPolynomial.C (a r)) := by
    intro r
    simp [φ, base]
  have hφmap : ∀ P : MvPolynomial ν R,
      φ (MvPolynomial.map (Ideal.Quotient.mk c) P) = mkJ (MvPolynomial.map a P) := by
    intro P
    have h : φ.comp (MvPolynomial.map (Ideal.Quotient.mk c)) = mkJ.comp (MvPolynomial.map a) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply, MvPolynomial.map_C]
        exact hφC r
      · intro s
        simp [φ]
    exact RingHom.congr_fun h P
  let q : MvPolynomial ν (R ⧸ c) →+* D := (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D)
  have hkerφ : RingHom.ker q ≤ RingHom.ker φ := by
    have hq : RingHom.ker q = Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)) := by
      rw [← hker]; rfl
    rw [hq, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hφmap, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.subset_span ⟨s, rfl⟩)
  let dA : D →+* MvPolynomial ν R' ⧸ J :=
    q.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨φ, hkerφ⟩
  have hdA : ∀ p, dA (q p) = φ p := fun p =>
    RingHom.liftOfRightInverse_comp_apply q _ _ ⟨φ, hkerφ⟩ p
  have hqX : ∀ s, q (MvPolynomial.X s) = ζ s := fun s => by simp [q]
  have hqC : ∀ x : R ⧸ c, q (MvPolynomial.C x) = algebraMap (R ⧸ c) D x := fun x => by
    simp [q]
  have w : CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) ≫ CommRingCat.ofHom dA =
      CommRingCat.ofHom a ≫ CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R')) := by
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [← hqC, hdA, hφC]
  let desc := hpo.desc (CommRingCat.ofHom dA) (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w
  have hinl : ∀ x : D, desc.hom (ψ x) = dA x := fun x => by
    have := congrArg (fun f => f.hom x) (hpo.inl_desc (CommRingCat.ofHom dA)
      (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    exact this
  have hinr : ∀ x : R', desc.hom (χ x) = mkJ (MvPolynomial.C x) := fun x => by
    have := congrArg (fun f => f.hom x) (hpo.inr_desc (CommRingCat.ofHom dA)
      (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    exact this
  have hΦ : desc.hom.comp (MvPolynomial.eval₂Hom χ (fun s ↦ ψ (ζ s))) = mkJ := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact hinr x
    · intro s
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [hinl, ← hqX, hdA]
      simp [φ]
  have h0 : mkJ G = 0 := by
    rw [← hΦ, RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, hG, map_zero]
  exact (Ideal.Quotient.eq_zero_iff_mem).1 h0

end GlobalTheory.PinchKernel
