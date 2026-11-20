import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.BlockForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FiniteOfGeneratedByOneElement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ResSqField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.TwoBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ZlUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SpanDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SpanInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FlagBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ConjCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ClosedOfComb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SolBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] {n a : ℕ}

/- English proof (translation)
Introduce `i j`. Use `⟨fun _ => trivial, fun e => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_bot, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : ((i : ℕ) < a ↔ (k : ℕ) < a)`.

Establish `h0 : Z k j = 0` using `(hZ k j).2 fun h' => e (h.trans h')`. Rewrite using `[h0, mul_zero]`. Establish `h0 : Y i k = 0` using `(hY i k).2 h`. Rewrite using `[h0, zero_mul]`.
-/
private theorem ev_mul {Y Z : Matrix (Fin n) (Fin n) R} (hY : Y ∈ Ev R R n a) (hZ : Z ∈ Ev R R n a) :
    Y * Z ∈ Ev R R n a := by
  intro i j
  refine ⟨fun _ => trivial, fun e => ?_⟩
  rw [Submodule.mem_bot, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : ((i : ℕ) < a ↔ (k : ℕ) < a)
  · have h0 : Z k j = 0 := (hZ k j).2 fun h' => e (h.trans h')
    rw [h0, mul_zero]
  · have h0 : Y i k = 0 := (hY i k).2 h
    rw [h0, zero_mul]

/- English proof (translation)
Introduce `i j` and use `⟨fun _ => trivial, fun e => (hY j i).2 fun h => e h.symm⟩`.
-/
private theorem ev_tr {Y : Matrix (Fin n) (Fin n) R} (hY : Y ∈ Ev R R n a) : Yᵀ ∈ Ev R R n a :=
  fun i j => ⟨fun _ => trivial, fun e => (hY j i).2 fun h => e h.symm⟩

/- English proof (translation)
Introduce `i j`. Use `⟨fun _ => trivial, fun e => ?_⟩` and prove the remaining obligations. Establish `h0 : Z i j = 0` using `(hZ i j).2 e`. Rewrite using `[Submodule.mem_bot, Matrix.map_apply, h0, map_zero]`.
-/
private theorem ev_map (f : R →+* S) {Z : Matrix (Fin n) (Fin n) R} (hZ : Z ∈ Ev R R n a) : Z.map f ∈ Ev S S n a := by
  intro i j
  refine ⟨fun _ => trivial, fun e => ?_⟩
  have h0 : Z i j = 0 := (hZ i j).2 e
  rw [Submodule.mem_bot, Matrix.map_apply, h0, map_zero]

/- English proof (translation)
Set `c : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R` to `(LinearMap.mulRight R T).comp (LinearMap.mulLeft R Ti)`. Establish `hc : ∀ Z, c Z = Ti * Z * T` using `fun Z => rfl`. Establish `e : (Set.range fun i => Ti * r i * T) = c '' Set.range r`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression.

Rewrite using `[e, ← Submodule.map_span, h]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨Z, hZ, rfl⟩`. Conclude with `ev_mul (ev_mul hTi hZ) hT`. Introduce `Z hZ`.

Use `⟨T * Z * Ti, ev_mul (ev_mul hT hZ) hTi, ?_⟩` and prove the remaining obligations. Rewrite using `[hc]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem span_conj {ι : Type} (r : ι → Matrix (Fin n) (Fin n) R) (T Ti : Matrix (Fin n) (Fin n) R)
    (h1 : Ti * T = 1) (hT : T ∈ Ev R R n a) (hTi : Ti ∈ Ev R R n a)
    (h : Submodule.span R (Set.range r) = Ev R R n a) :
    Submodule.span R (Set.range fun i => Ti * r i * T) = Ev R R n a := by
  let c : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R :=
    (LinearMap.mulRight R T).comp (LinearMap.mulLeft R Ti)
  have hc : ∀ Z, c Z = Ti * Z * T := fun Z => rfl
  have e : (Set.range fun i => Ti * r i * T) = c '' Set.range r := by
    rw [← Set.range_comp]; rfl
  rw [e, ← Submodule.map_span, h]
  apply le_antisymm
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ev_mul (ev_mul hTi hZ) hT
  · intro Z hZ
    refine ⟨T * Z * Ti, ev_mul (ev_mul hT hZ) hTi, ?_⟩
    rw [hc]
    calc Ti * (T * Z * Ti) * T = (Ti * T) * Z * (Ti * T) := by simp only [Matrix.mul_assoc]
      _ = Z := by rw [h1, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Establish `h2 : Tiᵀ * Tᵀ = 1` using `by rw [← transpose_mul, h1, transpose_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, h2, Matrix.mul_one, Matrix.mul_one, h, Matrix.mul_smul, Matrix.smul_mul]`.
-/
private theorem form_conj (A B P T Ti : Matrix (Fin n) (Fin n) R) (u : R) (h1 : T * Ti = 1) (h : Aᵀ * P * B = u • P) :
    (Ti * A * T)ᵀ * (Tᵀ * P * T) * (Ti * B * T) = u • (Tᵀ * P * T) := by
  have h2 : Tiᵀ * Tᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
  calc (Ti * A * T)ᵀ * (Tᵀ * P * T) * (Ti * B * T)
      = Tᵀ * (Aᵀ * (Tiᵀ * Tᵀ) * P * (T * Ti) * B) * T := by simp only [transpose_mul, Matrix.mul_assoc]
    _ = u • (Tᵀ * P * T) := by
      rw [h1, h2, Matrix.mul_one, Matrix.mul_one, h, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Rewrite using `[← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
private theorem form_map (f : R →+* S) (A B P : Matrix (Fin n) (Fin n) R) (u : R) (h : Aᵀ * P * B = u • P) :
    (A.map f)ᵀ * P.map f * B.map f = f u • P.map f := by
  rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h]
  ext i j
  simp

/- English proof (translation)
Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) (fun p : Fin n × Fin n => M p.1 p.2)`. Use `choose P hP using hd`. Use `⟨d, nonZeroDivisors.coe_ne_zero d, Matrix.of fun a b => P (a, b), ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Simplify using `only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, hP, Algebra.smul_def]`.

Both sides reduce to the same expression.
-/
private theorem clear_den [IsDomain R] (M : Matrix (Fin n) (Fin n) (FractionRing R)) :
    ∃ d : R, d ≠ 0 ∧ ∃ P : Matrix (Fin n) (Fin n) R,
      P.map (algebraMap R (FractionRing R)) = algebraMap R (FractionRing R) d • M := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : Fin n × Fin n => M p.1 p.2)
  choose P hP using hd
  refine ⟨d, nonZeroDivisors.coe_ne_zero d, Matrix.of fun a b => P (a, b), ?_⟩
  ext a b
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, hP, Algebra.smul_def]
  rfl

/- English proof (translation)
Take `⟨d, hd, P, hP⟩` from `clear_den M`. Take `⟨d', hd', P', hP'⟩` from `clear_den N`. Use `⟨d * d', mul_ne_zero hd hd', fun Z i i' => ⟨(P * Z * P') i i', ?_⟩⟩` and prove the remaining obligations. Establish `: (P * Z * P').map (algebraMap R (FractionRing R)) = algebraMap R (FractionRing R) (d * d') • (M * Z.map (algebraMap R (FractionRing R)) * N)`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hP, hP', Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_mul]`.

Conclude with `(congrFun (congrFun this i) i').symm`.
-/
private theorem bdd_den [IsDomain R] (M N : Matrix (Fin n) (Fin n) (FractionRing R)) :
    ∃ d : R, d ≠ 0 ∧ ∀ (Z : Matrix (Fin n) (Fin n) R) i i', ∃ y : R,
      algebraMap R (FractionRing R) d * (M * Z.map (algebraMap R (FractionRing R)) * N) i i' =
        algebraMap R (FractionRing R) y := by
  obtain ⟨d, hd, P, hP⟩ := clear_den M
  obtain ⟨d', hd', P', hP'⟩ := clear_den N
  refine ⟨d * d', mul_ne_zero hd hd', fun Z i i' => ⟨(P * Z * P') i i', ?_⟩⟩
  have : (P * Z * P').map (algebraMap R (FractionRing R)) =
      algebraMap R (FractionRing R) (d * d') • (M * Z.map (algebraMap R (FractionRing R)) * N) := by
    rw [Matrix.map_mul, Matrix.map_mul, hP, hP', Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_mul]
  exact (congrFun (congrFun this i) i').symm

/- English proof (translation)
Establish `hi : Function.Injective ((algebraMap S (FractionRing S)).comp j)` using `(IsFractionRing.injective S (FractionRing S)).comp hj`. Conclude with `⟨IsFractionRing.lift (K := FractionRing R) hi, fun y => IsFractionRing.lift_algebraMap hi y⟩`.
-/
private theorem frac_ext [IsDomain R] [IsDomain S] (j : R →+* S) (hj : Function.Injective j) :
    ∃ f : FractionRing R →+* FractionRing S, ∀ y, f (algebraMap _ _ y) = algebraMap _ _ (j y) := by
  have hi : Function.Injective ((algebraMap S (FractionRing S)).comp j) :=
    (IsFractionRing.injective S (FractionRing S)).comp hj
  exact ⟨IsFractionRing.lift (K := FractionRing R) hi, fun y => IsFractionRing.lift_algebraMap hi y⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(GDet.repAlg ρ (Polynomial R) _).det = _`. Rewrite using `[map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]`. Use `congr 1`. Use extensionality with `i j : 2`. Apply the tactic sequence `by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]`.
-/
private theorem chi_ofRep {G : Type} [Group G] (ρ : G →* Matrix (Fin n) (Fin n) R) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial R) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

/- English proof (translation)
Use `GDet.ext fun C _ _ x => ?_` and prove the remaining obligations. Use `letI : Algebra R C := ((algebraMap S C).comp f).toAlgebra`. Express the relevant statement in the definitionally equal form `(GDet.repAlg ρ C x).det = (GDet.repAlg _ C x).det`. Use `congr 2`.
-/
private theorem map_ofRep {G : Type} [Group G] (ρ : G →* Matrix (Fin n) (Fin n) R)
    (f : R →+* S) : (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  refine GDet.ext fun C _ _ x => ?_
  letI : Algebra R C := ((algebraMap S C).comp f).toAlgebra
  change (GDet.repAlg ρ C x).det = (GDet.repAlg _ C x).det
  congr 2

/- English proof (translation)
Rewrite using `[map_ofRep]`. Use `UpperTheory.V.CA.d_gext _ _ fun g i _ _ => ?_` and prove the remaining obligations. Rewrite using `[GDet.lam, GDet.lam, chi_ofRep, chi_ofRep, h, ← Matrix.charpoly_map]`. Both sides reduce to the same expression.
-/
private theorem det_of_charpoly {G : Type} [Group G] (ρ : G →* Matrix (Fin n) (Fin n) R)
    (ρ' : G →* Matrix (Fin n) (Fin n) S) (f : R →+* S) (h : ∀ g, (ρ' g).charpoly = (ρ g).charpoly.map f) :
    GDet.ofRep ρ' = (GDet.ofRep ρ).map f := by
  rw [map_ofRep]
  refine UpperTheory.V.CA.d_gext _ _ fun g i _ _ => ?_
  rw [GDet.lam, GDet.lam, chi_ofRep, chi_ofRep, h, ← Matrix.charpoly_map]
  rfl

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `g`. Use `⟨F.conj g, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = g`. Establish `h : F.c⁻¹ * F.c⁻¹ = 1` using `by rw [← _root_.mul_inv_rev, F.c_sq, inv_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem conj_surj {l : ℕ} [Fact l.Prime] (F : GFrame l) : Function.Surjective F.conj := by
  intro g
  refine ⟨F.conj g, Subtype.ext ?_⟩
  change F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = g
  have h : F.c⁻¹ * F.c⁻¹ = 1 := by rw [← _root_.mul_inv_rev, F.c_sq, inv_one]
  calc F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = (F.c * F.c) * g * (F.c⁻¹ * F.c⁻¹) := by simp only [mul_assoc]
    _ = g := by rw [h, F.c_sq, one_mul, mul_one]

/- English proof (translation)
Take `⟨a, Q, ha1, han, haI, hev, hspan, hH⟩` from `Det.blockForm x hn hx`. Take `⟨j₁, i₁, l₁, fin₁, hX⟩` from `Det.sqExt (K := x.K)`. Take `⟨K', _, _, j₂, i₂, l₂, fin₂, hsq⟩` from `Det.resSq (K := x.K)`. Take `⟨f₁, hf₁⟩` from `frac_ext j₁ i₁`. Take `⟨f₂, hf₂⟩` from `frac_ext j₂ i₂`.

Establish `hch : CharP x.K l` using `(Det.zlUniq l).1 ((algebraMap O x.K).comp (algebraMap ℤ_[l] O))`. Establish `h2 : (2 : x.K) ≠ 0`. Introduce `h`. Establish `h' : ((2 : ℕ) : x.K) = 0` using `by exact_mod_cast h`. Rewrite `h'` using `[CharP.cast_eq_zero_iff x.K l]`.

Conclude with `hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')`. Take `⟨d, hd, hden⟩` from `bdd_den (R := x.A) (Q : Matrix (Fin n) (Fin n) x.Fr) ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)`. Set `rQ : F.G₀ →* GL (Fin n) x.Fr` to `(MulAut.conj Q).toMonoidHom.comp x.ρF`. Establish `hrQ : ∀ g, mat rQ g = (Q : Matrix (Fin n) (Fin n) x.Fr) * (mat x.ρ g).map (algebraMap x.A x.Fr) * ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)` using `fun g => rfl`. Use `set PF := (x.P : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr) with hPF`.

Establish `hPd : PF.det ≠ 0` using `(Matrix.isUnits_det_units (GeneralLinearGroup.map (algebraMap x.A x.Fr) x.P)).ne_zero`. Establish `hQd : ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr).det ≠ 0` using `(Matrix.isUnits_det_units Q⁻¹).ne_zero`. Establish `hPs : PFᵀ = PF` using `by rw [hPF, ← transpose_map, x.symm]`. Take `⟨Q', ρ', e1, e2, e3, e4⟩` from `Det.twoBlock a j₁ f₁ j₂ f₂ rQ _ F.conj (fun g => ((F.eps O x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A)) d h2 hf₁ hf₂ hX hsq hd (fun g i i' => hden (mat x.ρ g) i i') (by rw [transpose_mul, transpose_mul, transpose_transpose, hPs, Matrix.mul_assoc]) (by rw [det_mul, det_mul, det_transpose …`. Rewrite using `[hrQ, hrQ]`.

Conclude with `form_conj _ _ _ _ _ _ (Units.inv_mul Q) (form_map _ _ _ _ _ (x.form g)))`. Use `han hev hH`. Establish `e2' : ∀ g, pushRep (algebraMap _ (FractionRing (PowerSeries K'))) ρ' g = Q'⁻¹ * pushRep (f₂.comp f₁) rQ g * Q'` using `fun g => by`. Rewrite using `[mul_assoc, e2, inv_mul_cancel_left]`. Use `⟨K', inferInstance, inferInstance, j₂.comp j₁, f₂.comp f₁, a, GeneralLinearGroup.map (f₂.comp f₁) Q⁻¹ * Q', ρ', i₂.comp i₁, inferInstance, fin₂.comp fin₁, fun y => by rw [RingHom.comp_apply, hf₁, hf₂, RingHom.comp_apply], ha1, han, haI, fun g => ?_, ?_, e4, ?_⟩` and prove the remaining obligations.

Rewrite using `[e2']`. Express the relevant statement in the definitionally equal form `Q'⁻¹ * GeneralLinearGroup.map (f₂.comp f₁) (Q * x.ρF g * Q⁻¹) * Q' = _ * GeneralLinearGroup.map (f₂.comp f₁) (x.ρF g) * _`. Simplify using `only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]`. Rewrite using `[← e1, Units.val_mul, transpose_mul, Matrix.map_mul, Matrix.map_mul, transpose_map]`. Simplify using `only [Matrix.mul_assoc]`.

Both sides reduce to the same expression. Establish `hi : ((Q'⁻¹ : GL (Fin n) (FractionRing (PowerSeries K'))) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) ∈ Ev (FractionRing (PowerSeries K')) (FractionRing (PowerSeries K')) n a`. Rewrite using `[Units.inv_eq_of_mul_eq_one_left e1]`. Conclude with `ev_mul (ev_tr e3) (ev_map _ hH)`. Rewrite `hspan`, the goal using `[Set.image_eq_range]`.

Establish `h3` using `(Det.spanDesc (f₂.comp f₁) _ fun g : (F.G' : Set F.G₀) => hev g).1 hspan`. Rewrite using `[← span_conj _ _ _ (Units.inv_mul Q') e3 hi h3]`. Use `congr 2`. Use function extensionality and compare the values at `g`. Conclude with `congrArg Units.val (e2' g)`.
-/
private theorem core {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {n : ℕ} {r : Resid F O n} (x : Point r) (hl : l ≠ 2) (hn : 0 < n) (hx : x.TypeI ∨ x.TypeE) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (j : x.A →+* PowerSeries K')
      (f : x.Fr →+* FractionRing (PowerSeries K')) (a : ℕ) (T : GL (Fin n) (FractionRing (PowerSeries K')))
      (ρ' : F.G₀ →* GL (Fin n) (PowerSeries K')),
      Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ (∀ y, f (algebraMap _ _ y) = algebraMap _ _ (j y)) ∧
      1 ≤ a ∧ a ≤ n ∧ (x.TypeI → a = n) ∧
      (∀ g, pushRep (algebraMap _ (FractionRing (PowerSeries K'))) ρ' g = T⁻¹ * pushRep f x.ρF g * T) ∧
      (T : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K')))ᵀ *
        ((x.P : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr)).map f * T = 1 ∧
      (∀ g, mat ρ' g ∈ Ev (PowerSeries K') (PowerSeries K') n a) ∧
      Submodule.span (FractionRing (PowerSeries K'))
        ((fun g => (mat ρ' g).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K')))) '' (F.G' : Set F.G₀)) =
        Ev (FractionRing (PowerSeries K')) (FractionRing (PowerSeries K')) n a := by
  obtain ⟨a, Q, ha1, han, haI, hev, hspan, hH⟩ := Det.blockForm x hn hx
  obtain ⟨j₁, i₁, l₁, fin₁, hX⟩ := Det.sqExt (K := x.K)
  obtain ⟨K', _, _, j₂, i₂, l₂, fin₂, hsq⟩ := Det.resSq (K := x.K)
  obtain ⟨f₁, hf₁⟩ := frac_ext j₁ i₁
  obtain ⟨f₂, hf₂⟩ := frac_ext j₂ i₂
  have hch : CharP x.K l := (Det.zlUniq l).1 ((algebraMap O x.K).comp (algebraMap ℤ_[l] O))
  have h2 : (2 : x.K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : x.K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff x.K l] at h'
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')
  obtain ⟨d, hd, hden⟩ := bdd_den (R := x.A) (Q : Matrix (Fin n) (Fin n) x.Fr) ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)
  let rQ : F.G₀ →* GL (Fin n) x.Fr := (MulAut.conj Q).toMonoidHom.comp x.ρF
  have hrQ : ∀ g, mat rQ g = (Q : Matrix (Fin n) (Fin n) x.Fr) * (mat x.ρ g).map (algebraMap x.A x.Fr) *
      ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) := fun g => rfl
  set PF := (x.P : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr) with hPF
  have hPd : PF.det ≠ 0 := (Matrix.isUnits_det_units (GeneralLinearGroup.map (algebraMap x.A x.Fr) x.P)).ne_zero
  have hQd : ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr).det ≠ 0 := (Matrix.isUnits_det_units Q⁻¹).ne_zero
  have hPs : PFᵀ = PF := by rw [hPF, ← transpose_map, x.symm]
  obtain ⟨Q', ρ', e1, e2, e3, e4⟩ := Det.twoBlock a j₁ f₁ j₂ f₂ rQ _ F.conj
    (fun g => ((F.eps O x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A)) d h2 hf₁ hf₂ hX hsq hd
    (fun g i i' => hden (mat x.ρ g) i i')
    (by rw [transpose_mul, transpose_mul, transpose_transpose, hPs, Matrix.mul_assoc])
    (by rw [det_mul, det_mul, det_transpose]; exact mul_ne_zero (mul_ne_zero hQd hPd) hQd)
    (conj_surj F)
    (fun g => by
      rw [hrQ, hrQ]
      exact form_conj _ _ _ _ _ _ (Units.inv_mul Q) (form_map _ _ _ _ _ (x.form g)))
    han hev hH
  have e2' : ∀ g, pushRep (algebraMap _ (FractionRing (PowerSeries K'))) ρ' g =
      Q'⁻¹ * pushRep (f₂.comp f₁) rQ g * Q' := fun g => by
    rw [mul_assoc, e2, inv_mul_cancel_left]
  refine ⟨K', inferInstance, inferInstance, j₂.comp j₁, f₂.comp f₁, a,
    GeneralLinearGroup.map (f₂.comp f₁) Q⁻¹ * Q', ρ', i₂.comp i₁, inferInstance, fin₂.comp fin₁,
    fun y => by rw [RingHom.comp_apply, hf₁, hf₂, RingHom.comp_apply], ha1, han, haI, fun g => ?_, ?_, e4, ?_⟩
  · rw [e2']
    change Q'⁻¹ * GeneralLinearGroup.map (f₂.comp f₁) (Q * x.ρF g * Q⁻¹) * Q' =
      _ * GeneralLinearGroup.map (f₂.comp f₁) (x.ρF g) * _
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
  · rw [← e1, Units.val_mul, transpose_mul, Matrix.map_mul, Matrix.map_mul, transpose_map]
    simp only [Matrix.mul_assoc]
    rfl
  · have hi : ((Q'⁻¹ : GL (Fin n) (FractionRing (PowerSeries K'))) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) ∈
        Ev (FractionRing (PowerSeries K')) (FractionRing (PowerSeries K')) n a := by
      rw [Units.inv_eq_of_mul_eq_one_left e1]
      exact ev_mul (ev_tr e3) (ev_map _ hH)
    rw [Set.image_eq_range] at hspan ⊢
    have h3 := (Det.spanDesc (f₂.comp f₁) _ fun g : (F.G' : Set F.G₀) => hev g).1 hspan
    rw [← span_conj _ _ _ (Units.inv_mul Q') e3 hi h3]
    congr 2
    funext g
    exact congrArg Units.val (e2' g)

/- English proof (translation)
Establish `h0` using `Det.solBase f e r h ((T : Matrix (Fin n) (Fin n) E') * Z.map φ * (T⁻¹ : GL (Fin n) E')) fun g => by`. Establish `e1` using `congrArg (fun Y => Matrix.map Y φ) (hZ g)`. Simplify using `only [Matrix.map_smul' _ _ _ (map_mul φ), Matrix.map_mul, hm, ← he] at e1`. Establish `e2` using `congrArg (fun Y => (T : Matrix (Fin n) (Fin n) E') * Y * (T⁻¹ : GL (Fin n) E')) e1`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, Matrix.mul_one] at e2 ⊢`.

Conclude with `e2`. Apply `Matrix.map_injective hφ` to reduce the goal to its premises. Establish `e2` using `congrArg (fun Y => ((T⁻¹ : GL (Fin n) E') : Matrix (Fin n) (Fin n) E') * Y * (T : Matrix (Fin n) (Fin n) E')) h0`. Simplify using `only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul] at e2`. Conclude with `e2.trans (Matrix.map_zero _ (map_zero _)).symm`.
-/
private theorem conjugation_descends_to_subring {E E' A ι : Type} [Field E] [Field E'] [CommRing A] {n : ℕ} (f : E →+* E') (φ : A →+* E')
    (hφ : Function.Injective φ) (T : GL (Fin n) E') (e : ι → E) (r : ι → Matrix (Fin n) (Fin n) E) (e' : ι → A)
    (r' : ι → Matrix (Fin n) (Fin n) A) (he : ∀ i, f (e i) = φ (e' i))
    (hm : ∀ i, (r' i).map φ = ((T⁻¹ : GL (Fin n) E') : Matrix (Fin n) (Fin n) E') * (r i).map f * T)
    (h : ∀ X : Matrix (Fin n) (Fin n) E, (∀ i, e i • (r i * X) = X * r i) → X = 0)
    (Z : Matrix (Fin n) (Fin n) A) (hZ : ∀ i, e' i • (r' i * Z) = Z * r' i) : Z = 0 := by
  have h0 := Det.solBase f e r h ((T : Matrix (Fin n) (Fin n) E') * Z.map φ * (T⁻¹ : GL (Fin n) E')) fun g => by
    have e1 := congrArg (fun Y => Matrix.map Y φ) (hZ g)
    simp only [Matrix.map_smul' _ _ _ (map_mul φ), Matrix.map_mul, hm, ← he] at e1
    have e2 := congrArg (fun Y => (T : Matrix (Fin n) (Fin n) E') * Y * (T⁻¹ : GL (Fin n) E')) e1
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv,
      Matrix.mul_one] at e2 ⊢
    exact e2
  apply Matrix.map_injective hφ
  have e2 := congrArg (fun Y => ((T⁻¹ : GL (Fin n) E') : Matrix (Fin n) (Fin n) E') * Y *
    (T : Matrix (Fin n) (Fin n) E')) h0
  simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, Matrix.mul_one, Matrix.mul_zero,
    Matrix.zero_mul] at e2
  exact e2.trans (Matrix.map_zero _ (map_zero _)).symm

/- English proof (translation)
Introduce `l _ F O _ _ _ n r x I hl hn hI hx`. Take `⟨h1, hT, h3, h4⟩ : x.N1 ∧ (x.TypeI ∨ x.TypeE) ∧ x.N3 ∧ x.N4` from `hx.elim (fun h => ⟨h.1, .inl h.2.1, h.2.2⟩) fun h => ⟨h.1, .inr h.2.1, h.2.2⟩`. Take `⟨K', _, _, j, f, a, T, ρ', jinj, jloc, jfin, hf, ha1, han, haI, hρ, hP, hev, hspan⟩` from `core x hl hn hT`. Use `letI : Algebra ℤ_[l] K' := ((PowerSeries.constantCoeff : PowerSeries K' →+* K').comp (j.comp ((algebraMap O x.A).comp (algebraMap ℤ_[l] O)))).toAlgebra`. Establish `hch : CharP K' l` using `(Det.zlUniq l).1 (algebraMap ℤ_[l] K')`.

Establish `hl0 : (l : PowerSeries K') = 0`. Rewrite using `[← map_natCast (PowerSeries.C : K' →+* PowerSeries K'), CharP.cast_eq_zero, map_zero]`. Establish `hl1 : (l : FractionRing (PowerSeries K')) = 0`. Rewrite using `[← map_natCast (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))), hl0, map_zero]`. Establish `ι` using `IsFractionRing.injective (PowerSeries K') (FractionRing (PowerSeries K'))`.

Establish `ιM : Function.Injective fun Z : Matrix (Fin n) (Fin n) (PowerSeries K') => Z.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K')))` using `Matrix.map_injective ι`. Establish `he : ∀ g, F.eps ℤ_[l] (PowerSeries K') g = Units.map (j : x.A →* PowerSeries K') (F.eps O x.A g)` using `fun g => Units.ext (DFunLike.congr_fun ((Det.zlUniq l).2 ((algebraMap ℤ_[l] (PowerSeries K')).comp (algebraMap ℤ_[l] ℤ_[l])) (j.comp ((algebraMap O x.A).comp (algebraMap ℤ_[l] O))) hl0).1 ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]))`. Establish `heF : ∀ g, f ((F.eps O x.Fr g : x.Frˣ) : x.Fr) = algebraMap (PowerSeries K') (FractionRing (PowerSeries K')) ((F.eps ℤ_[l] (PowerSeries K') g : (PowerSeries K')ˣ) : PowerSeries K')` using `fun g => DFunLike.congr_fun ((Det.zlUniq l).2 (f.comp ((algebraMap O x.Fr).comp (algebraMap ℤ_[l] O))) ((algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))).comp ((algebraMap ℤ_[l] (PowerSeries K')).comp (algebraMap ℤ_[l] ℤ_[l]))) hl1).1 ((F.ε g : ℤ_[l]ˣ) : ℤ_[l])`. Establish `hm : ∀ g, (mat ρ' g).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) = ((T⁻¹ : GL (Fin n) (FractionRing (PowerSeries K'))) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) * (mat x.ρF g).map f * T` using `fun g => congrArg Units.val (hρ g)`. Establish `hF : ∀ g, mat x.ρF g = (mat x.ρ g).map (algebraMap x.A x.Fr)` using `fun g => rfl`.

Establish `hfc : f.comp (algebraMap x.A x.Fr) = (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))).comp j` using `RingHom.ext hf`. Establish `hcp : ∀ g, (mat ρ' g).charpoly.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) = (mat x.ρF g).charpoly.map f` using `fun g => by`. Rewrite using `[← Matrix.charpoly_map, ← Matrix.charpoly_map, hm, Matrix.coe_units_inv, Matrix.charpoly_units_conj']`. Establish `hu : Function.Injective (Units.map (j : x.A →* PowerSeries K'))` using `Units.map_injective jinj`. Establish `hpush : ∀ {v} (χ χ' : F.Gv v →* x.Aˣ), pushCh j χ = pushCh j χ' → χ = χ'` using `fun χ χ' h => MonoidHom.ext fun g => hu (DFunLike.congr_fun h g)`.

Establish `hfl : ∀ v, HasFlag (pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) (ρ'.comp (F.φ v))) fun i => pushCh (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) (pushCh j (x.ψ v i))`. Introduce `v`. Take `⟨g₀, hg₀⟩` from `x.flag v`. Use `⟨GeneralLinearGroup.map f g₀ * T, fun s => ?_⟩` and prove the remaining obligations. Establish `e : GeneralLinearGroup.map f g₀ * T * pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) (ρ'.comp (F.φ v)) s * (GeneralLinearGroup.map f g₀ * T)⁻¹ = GeneralLinearGroup.map f (g₀ * x.ρF (F.φ v s) * g₀⁻¹)`.

Express the relevant statement in the definitionally equal form `_ * pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) ρ' (F.φ v s) * _ = _`. Rewrite using `[hρ, map_mul, map_mul, map_inv]`. Express the relevant statement in the definitionally equal form `_ * (_ * GeneralLinearGroup.map f (x.ρF (F.φ v s)) * _) * _ = _`. Use `group`. Rewrite using `[e]`.

Use `⟨fun i k h => ?_, fun i => ?_⟩` and prove the remaining obligations. Conclude with `(congrArg f ((hg₀ s).1 i k h)).trans (map_zero f)`. Conclude with `(congrArg f ((hg₀ s).2 i)).trans (hf _)`. Use `choose w ty hw htri using fun v => Det.flagBasis (a := a) (ρ'.comp (F.φ v)) (fun i => pushCh j (x.ψ v i)) (fun g => hev _) (fun i k h => by_contra fun hik => (h1 v).1 i k hik (hpush _ _ h)) (hfl v)`. Establish `hcont : ∀ i k, AdicCont (maximalIdeal (PowerSeries K')) fun g => mat ρ' g i k`.

Use `Det.conjCont j (fun g => mat x.ρ g) T (fun g => mat ρ' g) jloc x.cont fun g => ?_` and prove the remaining obligations. Rewrite using `[hm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, hF, Matrix.map_map, ← hfc]`. Both sides reduce to the same expression. Establish `hform : F.IsForm ℤ_[l] n ρ' 1`. Introduce `g`.

Apply `ιM` to reduce the goal to its premises. Establish `e` using `form_conj _ _ _ _ _ _ (Units.mul_inv T) (form_map f _ _ _ _ (form_map (algebraMap x.A x.Fr) _ _ _ _ (x.form g)))`. Rewrite `e` using `[hP, ← hF, ← hF, ← hm, ← hm, hf]`. Simplify using `only [Units.val_one, Matrix.map_mul, transpose_map, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[e, he, ← map_zpow (Units.map (j : x.A →* PowerSeries K')), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]`.

Both sides reduce to the same expression. Establish `hine : ∀ u, ∀ g ∈ I u, ρ' g = 1`. Introduce `u g hg`. Apply `Units.ext` to reduce the goal to its premises. Apply `ιM` to reduce the goal to its premises.

Establish `e` using `hm g`. Rewrite `e` using `[hF]`. Establish `e1 : mat x.ρ g = 1` using `congrArg Units.val (x.ine u g (hI u hg))`. Rewrite `e` using `[e1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Units.inv_mul]`. Conclude with `e.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm`.

Establish `hN3 : ∀ U : Set F.G₀, IsOpen U → (U ∩ (F.G' : Set F.G₀)).Nonempty → ∃ σ ∈ U ∩ (F.G' : Set F.G₀), ((mat ρ' σ).charpoly.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K')))).Separable` using `fun U hU hne => (h3 U hU hne).imp fun σ hσ => ⟨hσ.1, by rw [hcp]; exact hσ.2.map⟩`. Use `⟨{ K := K', ρ := ρ', cont := hcont, form := hform, a := a, a_pos := ha1, a_le := han, blk := hev, span := Det.spanInt _ _ hspan, ine := hine, ψ := fun v i => pushCh j (x.ψ v i), ψ_mu := fun v i g hg => ?_, w := w, ty := ty, w_blk := hw, tri := htri, N1 := fun v => ⟨fun i k hik h …` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Units.map (j : x.A →* PowerSeries K') (x.ψ v i g) = 1`. Rewrite using `[Det.psiMu x v i g hg, map_one]`. Use `(h1 v).2 i k hik (MonoidHom.ext fun g => hu ?_)` and prove the remaining obligations.

Establish `e : Units.map (j : x.A →* PowerSeries K') (x.ψ v i g) = Units.map (j : x.A →* PowerSeries K') (x.ψ v k g) * F.eps ℤ_[l] (PowerSeries K') (F.φ v g)` using `DFunLike.congr_fun h g`. Rewrite using `[e, he, ← map_mul]`. Both sides reduce to the same expression. Use `det_of_charpoly (mat x.ρ) (mat ρ') j fun g => Polynomial.map_injective _ ι ?_` and prove the remaining obligations. Rewrite using `[hcp, hF, Matrix.charpoly_map, Polynomial.map_map, Polynomial.map_map, hfc]`.

Conclude with `hN3`. Introduce `Z hZ`. Conclude with `conjugation_descends_to_subring f _ ι T (fun g : F.D0 => ((F.eps O x.Fr g : x.Frˣ) : x.Fr)) (fun g => mat x.ρF g) (fun g => ((F.eps ℤ_[l] (PowerSeries K') g : (PowerSeries K')ˣ) : PowerSeries K')) (fun g => mat ρ' g) (fun g => heF g) (fun g => hm g) (fun X hX => h4 X fun g hg => …`.
-/
theorem UpperTheory.V.Pa.norm :
    UpperTheory.V.Pa.Norm := by
  intro l _ F O _ _ _ n r x I hl hn hI hx
  obtain ⟨h1, hT, h3, h4⟩ : x.N1 ∧ (x.TypeI ∨ x.TypeE) ∧ x.N3 ∧ x.N4 :=
    hx.elim (fun h => ⟨h.1, .inl h.2.1, h.2.2⟩) fun h => ⟨h.1, .inr h.2.1, h.2.2⟩
  obtain ⟨K', _, _, j, f, a, T, ρ', jinj, jloc, jfin, hf, ha1, han, haI, hρ, hP, hev, hspan⟩ := core x hl hn hT
  letI : Algebra ℤ_[l] K' := ((PowerSeries.constantCoeff : PowerSeries K' →+* K').comp
    (j.comp ((algebraMap O x.A).comp (algebraMap ℤ_[l] O)))).toAlgebra
  have hch : CharP K' l := (Det.zlUniq l).1 (algebraMap ℤ_[l] K')
  have hl0 : (l : PowerSeries K') = 0 := by
    rw [← map_natCast (PowerSeries.C : K' →+* PowerSeries K'), CharP.cast_eq_zero, map_zero]
  have hl1 : (l : FractionRing (PowerSeries K')) = 0 := by
    rw [← map_natCast (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))), hl0, map_zero]
  have ι := IsFractionRing.injective (PowerSeries K') (FractionRing (PowerSeries K'))
  have ιM : Function.Injective fun Z : Matrix (Fin n) (Fin n) (PowerSeries K') =>
      Z.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) := Matrix.map_injective ι
  have he : ∀ g, F.eps ℤ_[l] (PowerSeries K') g = Units.map (j : x.A →* PowerSeries K') (F.eps O x.A g) := fun g =>
    Units.ext (DFunLike.congr_fun ((Det.zlUniq l).2 ((algebraMap ℤ_[l] (PowerSeries K')).comp (algebraMap ℤ_[l] ℤ_[l]))
      (j.comp ((algebraMap O x.A).comp (algebraMap ℤ_[l] O))) hl0).1 ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]))
  have heF : ∀ g, f ((F.eps O x.Fr g : x.Frˣ) : x.Fr) = algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))
      ((F.eps ℤ_[l] (PowerSeries K') g : (PowerSeries K')ˣ) : PowerSeries K') := fun g =>
    DFunLike.congr_fun ((Det.zlUniq l).2 (f.comp ((algebraMap O x.Fr).comp (algebraMap ℤ_[l] O)))
      ((algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))).comp
        ((algebraMap ℤ_[l] (PowerSeries K')).comp (algebraMap ℤ_[l] ℤ_[l]))) hl1).1 ((F.ε g : ℤ_[l]ˣ) : ℤ_[l])
  have hm : ∀ g, (mat ρ' g).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) =
      ((T⁻¹ : GL (Fin n) (FractionRing (PowerSeries K'))) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) *
        (mat x.ρF g).map f * T := fun g => congrArg Units.val (hρ g)
  have hF : ∀ g, mat x.ρF g = (mat x.ρ g).map (algebraMap x.A x.Fr) := fun g => rfl
  have hfc : f.comp (algebraMap x.A x.Fr) = (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))).comp j :=
    RingHom.ext hf
  have hcp : ∀ g, (mat ρ' g).charpoly.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) =
      (mat x.ρF g).charpoly.map f := fun g => by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, hm, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  have hu : Function.Injective (Units.map (j : x.A →* PowerSeries K')) := Units.map_injective jinj
  have hpush : ∀ {v} (χ χ' : F.Gv v →* x.Aˣ), pushCh j χ = pushCh j χ' → χ = χ' := fun χ χ' h =>
    MonoidHom.ext fun g => hu (DFunLike.congr_fun h g)
  have hfl : ∀ v, HasFlag (pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) (ρ'.comp (F.φ v)))
      fun i => pushCh (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) (pushCh j (x.ψ v i)) := by
    intro v
    obtain ⟨g₀, hg₀⟩ := x.flag v
    refine ⟨GeneralLinearGroup.map f g₀ * T, fun s => ?_⟩
    have e : GeneralLinearGroup.map f g₀ * T *
        pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) (ρ'.comp (F.φ v)) s *
        (GeneralLinearGroup.map f g₀ * T)⁻¹ = GeneralLinearGroup.map f (g₀ * x.ρF (F.φ v s) * g₀⁻¹) := by
      change _ * pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) ρ' (F.φ v s) * _ = _
      rw [hρ, map_mul, map_mul, map_inv]
      change _ * (_ * GeneralLinearGroup.map f (x.ρF (F.φ v s)) * _) * _ = _
      group
    rw [e]
    refine ⟨fun i k h => ?_, fun i => ?_⟩
    · exact (congrArg f ((hg₀ s).1 i k h)).trans (map_zero f)
    · exact (congrArg f ((hg₀ s).2 i)).trans (hf _)
  choose w ty hw htri using fun v => Det.flagBasis (a := a) (ρ'.comp (F.φ v)) (fun i => pushCh j (x.ψ v i))
    (fun g => hev _) (fun i k h => by_contra fun hik => (h1 v).1 i k hik (hpush _ _ h)) (hfl v)
  have hcont : ∀ i k, AdicCont (maximalIdeal (PowerSeries K')) fun g => mat ρ' g i k := by
    refine Det.conjCont j (fun g => mat x.ρ g) T (fun g => mat ρ' g) jloc x.cont fun g => ?_
    rw [hm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, hF, Matrix.map_map, ← hfc]
    rfl
  have hform : F.IsForm ℤ_[l] n ρ' 1 := by
    intro g
    apply ιM
    have e := form_conj _ _ _ _ _ _ (Units.mul_inv T) (form_map f _ _ _ _ (form_map (algebraMap x.A x.Fr) _ _ _ _ (x.form g)))
    rw [hP, ← hF, ← hF, ← hm, ← hm, hf] at e
    simp only [Units.val_one, Matrix.map_mul, transpose_map, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [e, he, ← map_zpow (Units.map (j : x.A →* PowerSeries K')), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have hine : ∀ u, ∀ g ∈ I u, ρ' g = 1 := by
    intro u g hg
    apply Units.ext
    apply ιM
    have e := hm g
    rw [hF] at e
    have e1 : mat x.ρ g = 1 := congrArg Units.val (x.ine u g (hI u hg))
    rw [e1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Units.inv_mul] at e
    exact e.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm
  have hN3 : ∀ U : Set F.G₀, IsOpen U → (U ∩ (F.G' : Set F.G₀)).Nonempty → ∃ σ ∈ U ∩ (F.G' : Set F.G₀),
      ((mat ρ' σ).charpoly.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K')))).Separable :=
    fun U hU hne => (h3 U hU hne).imp fun σ hσ => ⟨hσ.1, by rw [hcp]; exact hσ.2.map⟩
  refine ⟨{
      K := K', ρ := ρ', cont := hcont, form := hform, a := a, a_pos := ha1, a_le := han, blk := hev,
      span := Det.spanInt _ _ hspan, ine := hine, ψ := fun v i => pushCh j (x.ψ v i),
      ψ_mu := fun v i g hg => ?_, w := w, ty := ty, w_blk := hw, tri := htri,
      N1 := fun v => ⟨fun i k hik h => (h1 v).1 i k hik (hpush _ _ h), fun i k hik h => ?_⟩ },
    j, jinj, jloc, jfin, ?_, fun _ _ => rfl, ?_, ?_, haI⟩
  · change Units.map (j : x.A →* PowerSeries K') (x.ψ v i g) = 1
    rw [Det.psiMu x v i g hg, map_one]
  · refine (h1 v).2 i k hik (MonoidHom.ext fun g => hu ?_)
    have e : Units.map (j : x.A →* PowerSeries K') (x.ψ v i g) =
        Units.map (j : x.A →* PowerSeries K') (x.ψ v k g) * F.eps ℤ_[l] (PowerSeries K') (F.φ v g) :=
      DFunLike.congr_fun h g
    rw [e, he, ← map_mul]
    rfl
  · refine det_of_charpoly (mat x.ρ) (mat ρ') j fun g => Polynomial.map_injective _ ι ?_
    rw [hcp, hF, Matrix.charpoly_map, Polynomial.map_map, Polynomial.map_map, hfc]
  · exact hN3
  · intro Z hZ
    exact conjugation_descends_to_subring f _ ι T (fun g : F.D0 => ((F.eps O x.Fr g : x.Frˣ) : x.Fr)) (fun g => mat x.ρF g)
      (fun g => ((F.eps ℤ_[l] (PowerSeries K') g : (PowerSeries K')ˣ) : PowerSeries K')) (fun g => mat ρ' g)
      (fun g => heF g) (fun g => hm g) (fun X hX => h4 X fun g hg => hX ⟨g, hg⟩) Z fun g => hZ g g.2
