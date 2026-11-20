import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut

noncomputable section
open MvPolynomial TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafPolyPf

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.
-/
theorem one_tmul_algebraMap {P S A : Type} [CommRing P] [CommRing S] [CommRing A] [Algebra P S] [Algebra P A]
    (p : P) : (1 : S) ⊗ₜ[P] algebraMap P A p = algebraMap P S p ⊗ₜ[P] (1 : A) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

def kap (d e : ℕ) (R : Type) [CommRing R] :
    MvPolynomial (Fin d ⊕ Fin e) R →+* MvPolynomial (Fin d) (MvPolynomial (Fin e) R) :=
  eval₂Hom (C.comp C) (Sum.elim 0 fun i => C (X i))

/- English proof (translation)
Introduce `e d R A _ _ φ I x y h`. Take `⟨hψ, hI⟩` from `h`. Use `set ψ := MvPolynomial.eval₂Hom φ (Sum.elim x y) with hψdef`. Set `P` to `MvPolynomial (Fin d ⊕ Fin e) R`. Set `S` to `MvPolynomial (Fin d) (MvPolynomial (Fin e) R)`.

Set `Cc` to `MvPolynomial (Fin d) (A ⧸ I)`. Use `letI : Algebra P A := ψ.toAlgebra`. Use `letI : Algebra P S := (kap d e R).toAlgebra`. Establish `hb : (algebraMap S (S ⊗[P] A)).Etale` using `RingHom.IsStableUnderBaseChange.tensorProduct RingHom.Etale.isStableUnderBaseChange S hψ`. Establish `hx : ∀ j, x j ∈ I` using `fun j => hI ▸ Ideal.subset_span ⟨j, rfl⟩`.

Establish `hψX : ∀ i, ψ (X i) = Sum.elim x y i` using `fun i => by simp [ψ]`. Set `gy : MvPolynomial (Fin e) R →+* A ⧸ I` to `eval₂Hom ((Ideal.Quotient.mk I).comp φ) fun i => Ideal.Quotient.mk I (y i)`. Set `FS : S →+* Cc` to `eval₂Hom ((C : A ⧸ I →+* Cc).comp gy) X`. Set `ρ : P →+* Cc` to `(C : A ⧸ I →+* Cc).comp ((Ideal.Quotient.mk I).comp ψ)`. Use `letI : Algebra P Cc := ρ.toAlgebra`.

Establish `hFSC : ∀ p, FS (C p) = C (gy p)` using `fun p => MvPolynomial.eval₂Hom_C _ _ _`. Establish `hFSX : ∀ j, FS (X j) = X j` using `fun j => MvPolynomial.eval₂Hom_X' _ _ _`. Establish `hgC : ∀ r, gy (C r) = Ideal.Quotient.mk I (φ r)` using `fun r => MvPolynomial.eval₂Hom_C _ _ _`. Establish `hgX : ∀ i, gy (X i) = Ideal.Quotient.mk I (y i)` using `fun i => MvPolynomial.eval₂Hom_X' _ _ _`. Establish `kC : ∀ r, kap d e R (C r) = C (C r)` using `fun r => MvPolynomial.eval₂Hom_C _ _ _`.

Establish `kl : ∀ j, kap d e R (X (Sum.inl j)) = 0` using `fun j => MvPolynomial.eval₂Hom_X' _ _ _`. Establish `kr : ∀ i, kap d e R (X (Sum.inr i)) = C (X i)` using `fun i => MvPolynomial.eval₂Hom_X' _ _ _`. Establish `ψC : ∀ r, ψ (C r) = φ r` using `fun r => MvPolynomial.eval₂Hom_C _ _ _`. Establish `hFS : FS.comp (kap d e R) = ρ`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `r show FS (kap d e R (C r)) = C (Ideal.Quotient.mk I (ψ (C r)))`. Rewrite using `[kC, hFSC, hgC, ψC]`. Introduce and unpack `(j | i)`. Use `show FS (kap d e R (X (Sum.inl j))) = C (Ideal.Quotient.mk I (ψ (X (Sum.inl j))))`. Rewrite using `[kl, hψX, map_zero]`.

Simplify using `[Ideal.Quotient.eq_zero_iff_mem.mpr (hx j)]`. Use `show FS (kap d e R (X (Sum.inr i))) = C (Ideal.Quotient.mk I (ψ (X (Sum.inr i))))`. Rewrite using `[kr, hFSC, hgX, hψX]`. Both sides reduce to the same expression. Set `fS : S →ₐ[P] Cc` to `{ FS with commutes' := fun p => RingHom.congr_fun hFS p }`.

Set `fA : A →ₐ[P] Cc` to `{ (C : A ⧸ I →+* Cc).comp (Ideal.Quotient.mk I) with commutes' := fun _ => rfl }`. Set `F : S ⊗[P] A →+* Cc` to `(Algebra.TensorProduct.productMap fS fA).toRingHom`. Establish `hk : I ≤ RingHom.ker (Algebra.TensorProduct.includeRight (R` using `P) (A := S) (B := A)).toRingHom := by`. Rewrite using `[hI, Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Establish `h1 : x j = algebraMap P A (X (Sum.inl j))`. Rewrite using `[RingHom.algebraMap_toAlgebra, hψX]`. Both sides reduce to the same expression. Establish `h2 : algebraMap P S (X (Sum.inl j)) = 0`. Rewrite using `[RingHom.algebraMap_toAlgebra]`.

Conclude with `kl j`. Simplify using `only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]`. Rewrite using `[h1, one_tmul_algebraMap, h2, TensorProduct.zero_tmul]`. Set `G : Cc →+* S ⊗[P] A` to `eval₂Hom (Ideal.Quotient.lift I (Algebra.TensorProduct.includeRight (R := P) (A := S) (B := A)).toRingHom fun a ha => hk ha) fun j => X j ⊗ₜ[P] (1 : A)`. Establish `hF1 : ∀ s : S, F (s ⊗ₜ[P] (1 : A)) = FS s` using `fun s => by simp [F, fS, fA]`.

Establish `hGC : ∀ a, G (C (Ideal.Quotient.mk I a)) = (1 : S) ⊗ₜ[P] a` using `fun a => by erw [MvPolynomial.eval₂Hom_C]; rfl`. Establish `hGX : ∀ j, G (X j) = X j ⊗ₜ[P] (1 : A)` using `fun j => MvPolynomial.eval₂Hom_X' _ _ _`. Establish `hFG : F.comp G = RingHom.id Cc`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Simplify using `[F, G, fS, fA]`. Introduce `j show F (G (X j)) = X j`. Rewrite using `[hGX, hF1, hFSX]`. Establish `hS : (G.comp F).comp (Algebra.TensorProduct.includeLeftRingHom (R` using `P) (A := S) (B := A)) = Algebra.TensorProduct.includeLeftRingHom := by`.

Apply `MvPolynomial.ringHom_ext'` to reduce the goal to its premises. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r show G (F (C (C r) ⊗ₜ[P] (1 : A))) = C (C r) ⊗ₜ[P] (1 : A)`. Establish `e1 : φ r = algebraMap P A (C r)`. Rewrite using `[RingHom.algebraMap_toAlgebra]`.

Conclude with `(MvPolynomial.eval₂Hom_C _ _ _).symm`. Establish `e2 : algebraMap P S (C r) = C (C r)`. Rewrite using `[RingHom.algebraMap_toAlgebra]`. Conclude with `MvPolynomial.eval₂Hom_C _ _ _`. Rewrite using `[hF1, hFSC, hgC, hGC, e1, one_tmul_algebraMap, e2]`.

Introduce `i show G (F (C (X i) ⊗ₜ[P] (1 : A))) = C (X i) ⊗ₜ[P] (1 : A)`. Establish `e1 : y i = algebraMap P A (X (Sum.inr i))` using `by rw [RingHom.algebraMap_toAlgebra, hψX]; rfl`. Establish `e2 : algebraMap P S (X (Sum.inr i)) = C (X i)`. Rewrite using `[RingHom.algebraMap_toAlgebra]`. Conclude with `MvPolynomial.eval₂Hom_X' _ _ _`.

Rewrite using `[hF1, hFSC, hgX, hGC, e1, one_tmul_algebraMap, e2]`. Introduce `j show G (F (X j ⊗ₜ[P] (1 : A))) = X j ⊗ₜ[P] (1 : A)`. Rewrite using `[hF1, hFSX, hGX]`. Establish `hGF : G.comp F = RingHom.id _`. Use `RingHom.ext fun z => ?_` and prove the remaining obligations.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul s a`. Establish `hs` using `RingHom.congr_fun hS s`. Simplify using `only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply] at hs`.

Establish `ha : G (F ((1 : S) ⊗ₜ[P] a)) = (1 : S) ⊗ₜ[P] a`. Simplify using `[F, G, fS, fA]`. Use `erw [MvPolynomial.eval₂Hom_C]`. Both sides reduce to the same expression. Establish `hm : s ⊗ₜ[P] a = (s ⊗ₜ[P] (1 : A)) * ((1 : S) ⊗ₜ[P] a)` using `by simp`.

Rewrite using `[RingHom.id_apply, RingHom.comp_apply, hm, map_mul, map_mul, hs, ha]`. Consider the case `add u v hu hv => simp only [RingHom.comp_apply, RingHom.id_apply, map_add] at hu hv ⊢`. Rewrite using `[hu, hv]`. Set `E : S ⊗[P] A ≃+* Cc` to `RingEquiv.ofRingHom F G hFG hGF`. Set `σ : P ≃+* S` to `(MvPolynomial.sumAlgEquiv R (Fin d) (Fin e)).toRingEquiv`.

Establish `s1 : ∀ r, σ (C r) = C (C r)` using `fun r => MvPolynomial.sumAlgEquiv_C_inl (R := R) (S₁ := Fin d) (S₂ := Fin e) r`. Establish `s2 : ∀ j, σ (X (Sum.inl j)) = X j` using `fun j => MvPolynomial.sumAlgEquiv_X_inl (R := R) (S₁ := Fin d) (S₂ := Fin e) j`. Establish `s3 : ∀ i, σ (X (Sum.inr i)) = C (X i)` using `fun i => MvPolynomial.sumAlgEquiv_X_inr (R := R) (S₁ := Fin d) (S₂ := Fin e) i`. Establish `key : (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp ((Ideal.Quotient.mk I).comp φ)) (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i)))) = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))).comp σ.toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `r`. Express the relevant statement in the definitionally equal form `_ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (C r))`. Rewrite using `[s1]`. Simplify using `[E, F, fS]`. Use `erw [MvPolynomial.eval₂Hom_C]`.

Simplify using `[gy]`. Introduce and unpack `(j | i)`. Express the relevant statement in the definitionally equal form `_ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (X (Sum.inl j)))`. Rewrite using `[s2]`. Simplify using `[E, F, fS]`.

Use `erw [MvPolynomial.eval₂Hom_X']`. Express the relevant statement in the definitionally equal form `_ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (X (Sum.inr i)))`. Rewrite using `[s3]`. Simplify using `[E, F, fS]`. Use `erw [MvPolynomial.eval₂Hom_C]`.

Simplify using `[gy]`. Rewrite using `[key]`. Conclude with `RingHom.Etale.respectsIso.2 _ σ (RingHom.Etale.respectsIso.1 _ E hb)`.
-/
theorem leafPoly : LateralTheory.CohomologicalPurity.ChartCut.LeafPoly := by
  intro e d R A _ _ φ I x y h
  obtain ⟨hψ, hI⟩ := h
  set ψ := MvPolynomial.eval₂Hom φ (Sum.elim x y) with hψdef
  let P := MvPolynomial (Fin d ⊕ Fin e) R
  let S := MvPolynomial (Fin d) (MvPolynomial (Fin e) R)
  let Cc := MvPolynomial (Fin d) (A ⧸ I)
  letI : Algebra P A := ψ.toAlgebra
  letI : Algebra P S := (kap d e R).toAlgebra
  have hb : (algebraMap S (S ⊗[P] A)).Etale :=
    RingHom.IsStableUnderBaseChange.tensorProduct RingHom.Etale.isStableUnderBaseChange S hψ
  have hx : ∀ j, x j ∈ I := fun j => hI ▸ Ideal.subset_span ⟨j, rfl⟩
  have hψX : ∀ i, ψ (X i) = Sum.elim x y i := fun i => by simp [ψ]
  let gy : MvPolynomial (Fin e) R →+* A ⧸ I := eval₂Hom ((Ideal.Quotient.mk I).comp φ) fun i => Ideal.Quotient.mk I (y i)
  let FS : S →+* Cc := eval₂Hom ((C : A ⧸ I →+* Cc).comp gy) X
  let ρ : P →+* Cc := (C : A ⧸ I →+* Cc).comp ((Ideal.Quotient.mk I).comp ψ)
  letI : Algebra P Cc := ρ.toAlgebra
  have hFSC : ∀ p, FS (C p) = C (gy p) := fun p => MvPolynomial.eval₂Hom_C _ _ _
  have hFSX : ∀ j, FS (X j) = X j := fun j => MvPolynomial.eval₂Hom_X' _ _ _
  have hgC : ∀ r, gy (C r) = Ideal.Quotient.mk I (φ r) := fun r => MvPolynomial.eval₂Hom_C _ _ _
  have hgX : ∀ i, gy (X i) = Ideal.Quotient.mk I (y i) := fun i => MvPolynomial.eval₂Hom_X' _ _ _
  have kC : ∀ r, kap d e R (C r) = C (C r) := fun r => MvPolynomial.eval₂Hom_C _ _ _
  have kl : ∀ j, kap d e R (X (Sum.inl j)) = 0 := fun j => MvPolynomial.eval₂Hom_X' _ _ _
  have kr : ∀ i, kap d e R (X (Sum.inr i)) = C (X i) := fun i => MvPolynomial.eval₂Hom_X' _ _ _
  have ψC : ∀ r, ψ (C r) = φ r := fun r => MvPolynomial.eval₂Hom_C _ _ _
  have hFS : FS.comp (kap d e R) = ρ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show FS (kap d e R (C r)) = C (Ideal.Quotient.mk I (ψ (C r)))
      rw [kC, hFSC, hgC, ψC]
    · rintro (j | i)
      · show FS (kap d e R (X (Sum.inl j))) = C (Ideal.Quotient.mk I (ψ (X (Sum.inl j))))
        rw [kl, hψX, map_zero]; simp [Ideal.Quotient.eq_zero_iff_mem.mpr (hx j)]
      · show FS (kap d e R (X (Sum.inr i))) = C (Ideal.Quotient.mk I (ψ (X (Sum.inr i))))
        rw [kr, hFSC, hgX, hψX]; rfl
  let fS : S →ₐ[P] Cc := { FS with commutes' := fun p => RingHom.congr_fun hFS p }
  let fA : A →ₐ[P] Cc := { (C : A ⧸ I →+* Cc).comp (Ideal.Quotient.mk I) with commutes' := fun _ => rfl }
  let F : S ⊗[P] A →+* Cc := (Algebra.TensorProduct.productMap fS fA).toRingHom
  have hk : I ≤ RingHom.ker (Algebra.TensorProduct.includeRight (R := P) (A := S) (B := A)).toRingHom := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : x j = algebraMap P A (X (Sum.inl j)) := by
      rw [RingHom.algebraMap_toAlgebra, hψX]; rfl
    have h2 : algebraMap P S (X (Sum.inl j)) = 0 := by
      rw [RingHom.algebraMap_toAlgebra]; exact kl j
    simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply]
    rw [h1, one_tmul_algebraMap, h2, TensorProduct.zero_tmul]
  let G : Cc →+* S ⊗[P] A :=
    eval₂Hom (Ideal.Quotient.lift I (Algebra.TensorProduct.includeRight (R := P) (A := S) (B := A)).toRingHom
      fun a ha => hk ha) fun j => X j ⊗ₜ[P] (1 : A)
  have hF1 : ∀ s : S, F (s ⊗ₜ[P] (1 : A)) = FS s := fun s => by simp [F, fS, fA]
  have hGC : ∀ a, G (C (Ideal.Quotient.mk I a)) = (1 : S) ⊗ₜ[P] a := fun a => by
    erw [MvPolynomial.eval₂Hom_C]; rfl
  have hGX : ∀ j, G (X j) = X j ⊗ₜ[P] (1 : A) := fun j => MvPolynomial.eval₂Hom_X' _ _ _
  have hFG : F.comp G = RingHom.id Cc := by
    apply MvPolynomial.ringHom_ext
    · intro r
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      simp [F, G, fS, fA]
    · intro j
      show F (G (X j)) = X j
      rw [hGX, hF1, hFSX]
  have hS : (G.comp F).comp (Algebra.TensorProduct.includeLeftRingHom (R := P) (A := S) (B := A)) =
      Algebra.TensorProduct.includeLeftRingHom := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r
        show G (F (C (C r) ⊗ₜ[P] (1 : A))) = C (C r) ⊗ₜ[P] (1 : A)
        have e1 : φ r = algebraMap P A (C r) := by
          rw [RingHom.algebraMap_toAlgebra]; exact (MvPolynomial.eval₂Hom_C _ _ _).symm
        have e2 : algebraMap P S (C r) = C (C r) := by
          rw [RingHom.algebraMap_toAlgebra]; exact MvPolynomial.eval₂Hom_C _ _ _
        rw [hF1, hFSC, hgC, hGC, e1, one_tmul_algebraMap, e2]
      · intro i
        show G (F (C (X i) ⊗ₜ[P] (1 : A))) = C (X i) ⊗ₜ[P] (1 : A)
        have e1 : y i = algebraMap P A (X (Sum.inr i)) := by rw [RingHom.algebraMap_toAlgebra, hψX]; rfl
        have e2 : algebraMap P S (X (Sum.inr i)) = C (X i) := by
          rw [RingHom.algebraMap_toAlgebra]; exact MvPolynomial.eval₂Hom_X' _ _ _
        rw [hF1, hFSC, hgX, hGC, e1, one_tmul_algebraMap, e2]
    · intro j
      show G (F (X j ⊗ₜ[P] (1 : A))) = X j ⊗ₜ[P] (1 : A)
      rw [hF1, hFSX, hGX]
  have hGF : G.comp F = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
      have hs := RingHom.congr_fun hS s
      simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply] at hs
      have ha : G (F ((1 : S) ⊗ₜ[P] a)) = (1 : S) ⊗ₜ[P] a := by
        simp [F, G, fS, fA]; erw [MvPolynomial.eval₂Hom_C]; rfl
      have hm : s ⊗ₜ[P] a = (s ⊗ₜ[P] (1 : A)) * ((1 : S) ⊗ₜ[P] a) := by simp
      rw [RingHom.id_apply, RingHom.comp_apply, hm, map_mul, map_mul, hs, ha]
    | add u v hu hv => simp only [RingHom.comp_apply, RingHom.id_apply, map_add] at hu hv ⊢; rw [hu, hv]
  let E : S ⊗[P] A ≃+* Cc := RingEquiv.ofRingHom F G hFG hGF
  let σ : P ≃+* S := (MvPolynomial.sumAlgEquiv R (Fin d) (Fin e)).toRingEquiv
  have s1 : ∀ r, σ (C r) = C (C r) := fun r => MvPolynomial.sumAlgEquiv_C_inl (R := R) (S₁ := Fin d) (S₂ := Fin e) r
  have s2 : ∀ j, σ (X (Sum.inl j)) = X j := fun j => MvPolynomial.sumAlgEquiv_X_inl (R := R) (S₁ := Fin d) (S₂ := Fin e) j
  have s3 : ∀ i, σ (X (Sum.inr i)) = C (X i) := fun i => MvPolynomial.sumAlgEquiv_X_inr (R := R) (S₁ := Fin d) (S₂ := Fin e) i
  have key : (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp
      ((Ideal.Quotient.mk I).comp φ)) (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i)))) =
      (E.toRingHom.comp (algebraMap S (S ⊗[P] A))).comp σ.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; change _ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (C r)); rw [s1]; simp [E, F, fS]; erw [MvPolynomial.eval₂Hom_C]; simp [gy]
    · rintro (j | i)
      · change _ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (X (Sum.inl j))); rw [s2]; simp [E, F, fS]; erw [MvPolynomial.eval₂Hom_X']
      · change _ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (X (Sum.inr i))); rw [s3]; simp [E, F, fS]; erw [MvPolynomial.eval₂Hom_C]; simp [gy]
  rw [key]
  exact RingHom.Etale.respectsIso.2 _ σ (RingHom.Etale.respectsIso.1 _ E hb)

/- English proof (translation)
The claim follows from `leafPoly`.
-/
theorem LeafPoly_of : LateralTheory.CohomologicalPurity.ChartCut.LeafPoly := leafPoly

end LateralTheory.CohomologicalPurity.LeafPolyPf
