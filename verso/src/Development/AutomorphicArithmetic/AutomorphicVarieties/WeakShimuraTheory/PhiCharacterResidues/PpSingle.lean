import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.FlagRel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

/- English proof (translation)
Establish `h : (D.comap π).chi y = D.chi (MonoidAlgebra.mapDomainRingHom B π y)`. Express the relevant statement in the definitionally equal form `D.D B[X] (MonoidAlgebra.mapDomainRingHom B[X] π _) = D.D B[X] _`. Use `congr 1`. Rewrite using `[map_sub]`. Use `congr 1`.

Simplify using the standard rewrite rules. Proceed by induction on `y using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `single g r => simp`.

Rewrite using `[← h, ← (UpperTheory.V.AlgebraTools.Det.mapApi (D.comap π) f).1, hD, (UpperTheory.V.AlgebraTools.Det.repApi ρ).1]`.
-/
private theorem pp_chi {n : ℕ} {A B G H : Type} [CommRing A] [CommRing B] [Group G] [Group H] (f : B →+* A)
    (π : H →* G) (D : W.GDet n B G) (ρ : H →* Matrix (Fin n) (Fin n) A) (hD : (D.comap π).map f = W.GDet.ofRep ρ)
    (y : MonoidAlgebra B H) :
    (D.chi (MonoidAlgebra.mapDomainRingHom B π y)).map f =
      (W.GDet.repAlg ρ A (MonoidAlgebra.mapRingHom H f y)).charpoly := by
  have h : (D.comap π).chi y = D.chi (MonoidAlgebra.mapDomainRingHom B π y) := by
    change D.D B[X] (MonoidAlgebra.mapDomainRingHom B[X] π _) = D.D B[X] _
    congr 1
    rw [map_sub]
    congr 1
    · simp
    · induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | single g r => simp
  rw [← h, ← (UpperTheory.V.AlgebraTools.Det.mapApi (D.comap π) f).1, hD, (UpperTheory.V.AlgebraTools.Det.repApi ρ).1]

/- English proof (translation)
Simplify using `[W.GDet.repAlg, MonoidAlgebra.lift_single]`.
-/
private theorem pp_single {n : ℕ} {A H : Type} [CommRing A] [Group H] (ρ : H →* Matrix (Fin n) (Fin n) A) (g : H) (a : A) :
    W.GDet.repAlg ρ A (MonoidAlgebra.single g a) = a • ρ g := by
  simp [W.GDet.repAlg, MonoidAlgebra.lift_single]

/- English proof (translation)
Establish `e1 : MonoidAlgebra.single (π h) (1 : B) * MonoidAlgebra.mapDomainRingHom B π y = MonoidAlgebra.mapDomainRingHom B π (MonoidAlgebra.single h 1 * y)`. Rewrite using `[map_mul]`. Simplify using `[MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]`. Establish `e2 : W.GDet.repAlg ρ A (MonoidAlgebra.mapRingHom H f (MonoidAlgebra.single h 1 * y)) = 0`. Rewrite using `[map_mul, map_mul, hy, mul_zero]`.

Establish `hc` using `pp_chi f π D ρ hD (MonoidAlgebra.single h 1 * y)`. Rewrite `hc` using `[e2, Matrix.charpoly_zero, Fintype.card_fin]`. Rewrite using `[e1]`. Simplify using `only [W.GDet.tr, W.GDet.lam]`. Establish `h0 : f ((D.chi (MonoidAlgebra.mapDomainRingHom B π (MonoidAlgebra.single h 1 * y))).coeff (n - 1)) = 0`.

Rewrite using `[← Polynomial.coeff_map, hc, Polynomial.coeff_X_pow]`. Rewrite using `[if_neg (by omega)]`. Rewrite using `[(map_eq_zero_iff f hf).1 h0, mul_zero]`.
-/
private theorem pp_tr {n : ℕ} {A B G H : Type} [CommRing A] [CommRing B] [Group G] [Group H] (hn : 0 < n) (f : B →+* A)
    (hf : Function.Injective f)
    (π : H →* G) (D : W.GDet n B G) (ρ : H →* Matrix (Fin n) (Fin n) A) (hD : (D.comap π).map f = W.GDet.ofRep ρ)
    (h : H) (y : MonoidAlgebra B H) (hy : W.GDet.repAlg ρ A (MonoidAlgebra.mapRingHom H f y) = 0) :
    D.tr (MonoidAlgebra.single (π h) 1 * MonoidAlgebra.mapDomainRingHom B π y) = 0 := by
  have e1 : MonoidAlgebra.single (π h) (1 : B) * MonoidAlgebra.mapDomainRingHom B π y =
      MonoidAlgebra.mapDomainRingHom B π (MonoidAlgebra.single h 1 * y) := by
    rw [map_mul]
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  have e2 : W.GDet.repAlg ρ A (MonoidAlgebra.mapRingHom H f (MonoidAlgebra.single h 1 * y)) = 0 := by
    rw [map_mul, map_mul, hy, mul_zero]
  have hc := pp_chi f π D ρ hD (MonoidAlgebra.single h 1 * y)
  rw [e2, Matrix.charpoly_zero, Fintype.card_fin] at hc
  rw [e1]
  simp only [W.GDet.tr, W.GDet.lam]
  have h0 : f ((D.chi (MonoidAlgebra.mapDomainRingHom B π (MonoidAlgebra.single h 1 * y))).coeff (n - 1)) = 0 := by
    rw [← Polynomial.coeff_map, hc, Polynomial.coeff_X_pow]
    rw [if_neg (by omega)]
  rw [(map_eq_zero_iff f hf).1 h0, mul_zero]

set_option maxHeartbeats 200000 in
/- English proof (translation)
Introduce `l _ F O _ _ _ n r B A H _ _ _ _ _ _ _ _ hinj hn π hπ ρ D ψ hD hcont hred hpsi hstar hflag hI`. Use `⟨{ D := D, ψ := ψ, cont := hcont, red := ?_, psi := hpsi, P := ?_, Ord := ?_, I := ?_ }, rfl, rfl⟩` and prove the remaining obligations. Apply `CA.d_gext` to reduce the goal to its premises. Introduce `g i _ _`. Take `⟨g', rfl⟩` from `hπ g`.

Establish `h1 : (D.map (res O B : B →+* ResidueField O)).chi (MonoidAlgebra.single (π g') 1) = r.Dbar.chi (MonoidAlgebra.single (π g') 1)`. Use `(AlgebraTools.Det.mapApi D (res O B : B →+* ResidueField O)).1 (MonoidAlgebra.single (π g') 1)` as an intermediate fact. Rewrite `this` using `[MonoidAlgebra.mapRingHom_single, map_one]`. Rewrite using `[this, hred, W.Resid.Dbar, (AlgebraTools.Det.repApi _).2.1]`. Simplify using `[W.diagRep, Matrix.charpoly_diagonal]`.

Simplify using `only [W.GDet.lam, h1]`. Introduce `i g`. Take `⟨g0, rfl⟩` from `hπ g`. Take `⟨g', hg', hc⟩` from `hstar g0`. Establish `hs : F.star O B n (MonoidAlgebra.single (π g0) 1) = MonoidAlgebra.single (π g') ((F.eps O B (π g0) ^ (1 - (n : ℤ)) : Bˣ) : B)`.

Rewrite using `[hg']`. Simplify using `[W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single]`. Establish `he : algebraMap B A ((F.eps O B (π g0) ^ (1 - (n : ℤ)) : Bˣ) : B) = ((F.eps O A (π g0) ^ (1 - (n : ℤ)) : Aˣ) : A)`. Establish `hu : Units.map (algebraMap B A : B →* A) (F.eps O B (π g0)) = F.eps O A (π g0)`. Use `ext`.

Simplify using `[W.GFrame.eps, W.pushCh, IsScalarTower.algebraMap_apply O B A]`. Rewrite using `[← hu, ← map_zpow (Units.map (algebraMap B A : B →* A))]`. Both sides reduce to the same expression. Establish `h1` using `pp_chi (algebraMap B A) π D ρ hD (MonoidAlgebra.single g' ((F.eps O B (π g0) ^ (1 - (n : ℤ)) : Bˣ) : B))`. Establish `h2` using `pp_chi (algebraMap B A) π D ρ hD (MonoidAlgebra.single g0 1)`.

Rewrite `h1` using `[MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single, pp_single, he]`. Rewrite `h2` using `[MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single, pp_single, map_one, one_smul]`. Establish `hcc : D.chi (MonoidAlgebra.single (π g') ((F.eps O B (π g0) ^ (1 - (n : ℤ)) : Bˣ) : B)) = D.chi (MonoidAlgebra.single (π g0) 1)` using `Polynomial.map_injective _ hinj (by rw [h1, h2, hc])`. Simplify using `only [W.GDet.lam, hs, hcc]`. Introduce `v g h`.

Take `⟨j, hj, hfl⟩` from `hflag v`. Take `⟨h', rfl⟩` from `hπ h`. Establish `hz` using `(AlgebraTools.Det.flagRel _ _ hfl).2 g`. Establish `hy : W.GDet.repAlg ρ A (MonoidAlgebra.mapRingHom H (algebraMap B A) (List.ofFn fun i => MonoidAlgebra.single (j (g i)) (1 : B) - MonoidAlgebra.single 1 ((ψ v i (g i) : Bˣ) : B)).prod) = 0`. Rewrite using `[map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn, ← hz]`.

Use `congr 1`. Use `List.ofFn_inj.2 (funext fun i => ?_)` and prove the remaining obligations. Simplify using `[pp_single, MonoidAlgebra.mapRingHom_single, W.mat]`. Use `pp_tr hn (algebraMap B A) hinj π D ρ hD h' _ hy` as an intermediate fact. Establish `hj' : ∀ x, π (j x) = F.φ v x` using `fun x => by rw [← hj]; rfl`.

Establish `e : MonoidAlgebra.mapDomainRingHom B π (List.ofFn fun i => MonoidAlgebra.single (j (g i)) (1 : B) - MonoidAlgebra.single 1 ((ψ v i (g i) : Bˣ) : B)).prod = F.oEl v (ψ v) g`. Rewrite using `[map_list_prod, List.map_ofFn]`. Simplify using `only [W.GFrame.oEl]`. Use `congr 1`. Use `List.ofFn_inj.2 (funext fun i => ?_)` and prove the remaining obligations.

Rewrite using `[Function.comp_apply, map_sub, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single, hj', map_one]`. Rewrite `this` using `[e]`. Conclude with `this`. Introduce `u g hg h`. Take `⟨g', rfl, hg'⟩` from `hI u g hg`.

Take `⟨h', rfl⟩` from `hπ h`. Establish `hy : W.GDet.repAlg ρ A (MonoidAlgebra.mapRingHom H (algebraMap B A) (MonoidAlgebra.single g' 1 - 1)) = 0`. Rewrite using `[map_sub, map_one, MonoidAlgebra.mapRingHom_single, map_one, map_sub, pp_single, hg', one_smul, map_one, sub_self]`. Use `pp_tr hn (algebraMap B A) hinj π D ρ hD h' _ hy` as an intermediate fact. Establish `e : MonoidAlgebra.mapDomainRingHom B π (MonoidAlgebra.single g' (1 : B) - 1) = MonoidAlgebra.single (π g') 1 - 1`.

Rewrite using `[map_sub, map_one, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]`. Rewrite `this` using `[e]`. Conclude with `this`.
-/
theorem UpperTheory.V.Ws.phiPair :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} (r : W.Resid F O n) {B A H : Type} [CommRing B] [Algebra O B] [IsCO O B] [CommRing A] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Group H], Function.Injective (algebraMap B A) → 0 < n → ∀ (π : H →* F.G₀), Function.Surjective π → ∀ (ρ : H →* Matrix (Fin n) (Fin n) A) (D : W.GDet n B F.G₀) (ψ : ∀ v, Fin n → F.Gv v →* Bˣ), (D.comap π).map (algebraMap B A) = W.GDet.ofRep ρ → D.IsCont (maximalIdeal B) → (∀ g, (D.chi (MonoidAlgebra.single (π g) 1)).map (res O B : B →+* ResidueField O) = ∏ i, (Polynomial.X - C (r.chib i (π g) : ResidueField O))) → (∀ v i, r.IsPsi v i (ψ v i)) → (∀ g, ∃ g', π g' = (F.conj (π g))⁻¹ ∧ (((F.eps O A (π g) ^ (1 - (n : ℤ)) : Aˣ) : A) • ρ g').charpoly = (ρ g).charpoly) → (∀ v, ∃ j : F.Gv v →* H, π.comp j = F.φ v ∧ W.HasFlag (ρ.toHomUnits.comp j) fun i => W.pushCh (algebraMap B A) (ψ v i)) → (∀ u, ∀ g ∈ r.Ip u, ∃ g', π g' = g ∧ ρ g' = 1) → ∃ p : W.Pair r B, p.D = D ∧ p.ψ = ψ := by
  intro l _ F O _ _ _ n r B A H _ _ _ _ _ _ _ _ hinj hn π hπ ρ D ψ hD hcont hred hpsi hstar hflag hI
  refine ⟨{ D := D, ψ := ψ, cont := hcont, red := ?_, psi := hpsi, P := ?_, Ord := ?_, I := ?_ }, rfl, rfl⟩
  · apply CA.d_gext
    intro g i _ _
    obtain ⟨g', rfl⟩ := hπ g
    have h1 : (D.map (res O B : B →+* ResidueField O)).chi (MonoidAlgebra.single (π g') 1) =
        r.Dbar.chi (MonoidAlgebra.single (π g') 1) := by
      have := (AlgebraTools.Det.mapApi D (res O B : B →+* ResidueField O)).1 (MonoidAlgebra.single (π g') 1)
      rw [MonoidAlgebra.mapRingHom_single, map_one] at this
      rw [this, hred, W.Resid.Dbar, (AlgebraTools.Det.repApi _).2.1]
      simp [W.diagRep, Matrix.charpoly_diagonal]
    simp only [W.GDet.lam, h1]
  · intro i g
    obtain ⟨g0, rfl⟩ := hπ g
    obtain ⟨g', hg', hc⟩ := hstar g0
    have hs : F.star O B n (MonoidAlgebra.single (π g0) 1) =
        MonoidAlgebra.single (π g') ((F.eps O B (π g0) ^ (1 - (n : ℤ)) : Bˣ) : B) := by
      rw [hg']
      simp [W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single]
    have he : algebraMap B A ((F.eps O B (π g0) ^ (1 - (n : ℤ)) : Bˣ) : B) =
        ((F.eps O A (π g0) ^ (1 - (n : ℤ)) : Aˣ) : A) := by
      have hu : Units.map (algebraMap B A : B →* A) (F.eps O B (π g0)) = F.eps O A (π g0) := by
        ext
        simp [W.GFrame.eps, W.pushCh, IsScalarTower.algebraMap_apply O B A]
      rw [← hu, ← map_zpow (Units.map (algebraMap B A : B →* A))]
      rfl
    have h1 := pp_chi (algebraMap B A) π D ρ hD
      (MonoidAlgebra.single g' ((F.eps O B (π g0) ^ (1 - (n : ℤ)) : Bˣ) : B))
    have h2 := pp_chi (algebraMap B A) π D ρ hD (MonoidAlgebra.single g0 1)
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single,
      pp_single, he] at h1
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single,
      pp_single, map_one, one_smul] at h2
    have hcc : D.chi (MonoidAlgebra.single (π g') ((F.eps O B (π g0) ^ (1 - (n : ℤ)) : Bˣ) : B)) =
        D.chi (MonoidAlgebra.single (π g0) 1) :=
      Polynomial.map_injective _ hinj (by rw [h1, h2, hc])
    simp only [W.GDet.lam, hs, hcc]
  · intro v g h
    obtain ⟨j, hj, hfl⟩ := hflag v
    obtain ⟨h', rfl⟩ := hπ h
    have hz := (AlgebraTools.Det.flagRel _ _ hfl).2 g
    have hy : W.GDet.repAlg ρ A (MonoidAlgebra.mapRingHom H (algebraMap B A)
        (List.ofFn fun i => MonoidAlgebra.single (j (g i)) (1 : B) - MonoidAlgebra.single 1 ((ψ v i (g i) : Bˣ) : B)).prod) = 0 := by
      rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn, ← hz]
      congr 1
      refine List.ofFn_inj.2 (funext fun i => ?_)
      simp [pp_single, MonoidAlgebra.mapRingHom_single, W.mat]
    have := pp_tr hn (algebraMap B A) hinj π D ρ hD h' _ hy
    have hj' : ∀ x, π (j x) = F.φ v x := fun x => by rw [← hj]; rfl
    have e : MonoidAlgebra.mapDomainRingHom B π
        (List.ofFn fun i => MonoidAlgebra.single (j (g i)) (1 : B) - MonoidAlgebra.single 1 ((ψ v i (g i) : Bˣ) : B)).prod =
        F.oEl v (ψ v) g := by
      rw [map_list_prod, List.map_ofFn]
      simp only [W.GFrame.oEl]
      congr 1
      refine List.ofFn_inj.2 (funext fun i => ?_)
      rw [Function.comp_apply, map_sub, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single, hj', map_one]
    rw [e] at this
    exact this
  · intro u g hg h
    obtain ⟨g', rfl, hg'⟩ := hI u g hg
    obtain ⟨h', rfl⟩ := hπ h
    have hy : W.GDet.repAlg ρ A (MonoidAlgebra.mapRingHom H (algebraMap B A) (MonoidAlgebra.single g' 1 - 1)) = 0 := by
      rw [map_sub, map_one, MonoidAlgebra.mapRingHom_single, map_one, map_sub, pp_single, hg', one_smul, map_one, sub_self]
    have := pp_tr hn (algebraMap B A) hinj π D ρ hD h' _ hy
    have e : MonoidAlgebra.mapDomainRingHom B π (MonoidAlgebra.single g' (1 : B) - 1) = MonoidAlgebra.single (π g') 1 - 1 := by
      rw [map_sub, map_one, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
    rw [e] at this
    exact this
