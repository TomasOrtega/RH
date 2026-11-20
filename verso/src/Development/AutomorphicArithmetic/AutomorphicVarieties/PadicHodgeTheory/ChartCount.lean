import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtTangent
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DimZ1fCrystallineDeformation
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DefCoc
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

private noncomputable def jet {σ E : Type} [Field E] (i : σ) : MvPowerSeries σ E →ₐ[E] DualNumber E where
  toFun f := ⟨MvPowerSeries.constantCoeff f, MvPowerSeries.coeff (Finsupp.single i 1) f⟩
  map_one' := by
    classical
    ext
    · simp
    · simp [MvPowerSeries.coeff_one]
  map_mul' f g := by
    classical
    refine TrivSqZeroExt.ext (map_mul MvPowerSeries.constantCoeff f g) ?_
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    show MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
        MvPowerSeries.coeff (Finsupp.single i 1) f * MvPowerSeries.constantCoeff g
    simp [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.Nat.antidiagonal_succ, mul_comm]
  map_zero' := by ext <;> simp
  map_add' f g := TrivSqZeroExt.ext (map_add MvPowerSeries.constantCoeff f g) (map_add (MvPowerSeries.coeff _) f g)
  commutes' c := by
    classical
    ext <;> simp [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_sum]`.
-/
private theorem snd_mul_left {E : Type} [CommRing E] (A : Matrix (Fin 3) (Fin 3) E)
    (X : Matrix (Fin 3) (Fin 3) (DualNumber E)) :
    (A.map (algebraMap E (DualNumber E)) * X).map TrivSqZeroExt.snd = A * X.map TrivSqZeroExt.snd := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_sum]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_sum, mul_comm]`.
-/
private theorem snd_mul_right {E : Type} [CommRing E] (A : Matrix (Fin 3) (Fin 3) E)
    (X : Matrix (Fin 3) (Fin 3) (DualNumber E)) :
    (X * A.map (algebraMap E (DualNumber E))).map TrivSqZeroExt.snd = X.map TrivSqZeroExt.snd * A := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_sum, mul_comm]

/- English proof (translation)
Take `⟨γ, -, hc, hd⟩` from `exists_isCoc (RingHom.ker (TrivSqZeroExt.fstHom E E E)) ((GG.map (algebraMap E (DualNumber E))).comp r) r' (by`. Rewrite using `[eq_bot_iff, Ideal.mul_le]`. Introduce `x hx y hy`. Establish `hx' : x.fst = 0` using `hx`. Establish `hy' : y.fst = 0` using `hy`.

Rewrite using `[Ideal.mem_bot]`. Apply the tactic sequence `ext <;> simp [hx', hy']) (MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => by`. Use `Ideal.Quotient.eq.2 ?_` and prove the remaining obligations. Use `show ((r' g).mat a b - algebraMap E (DualNumber E) ((r g).mat a b)).fst = 0`. Simplify using `[h2, TrivSqZeroExt.algebraMap_eq_inl])) (h1 g))`.

Use `⟨fun g => (γ g).map TrivSqZeroExt.snd, fun g h => ?_, fun g => ⟨h1 g, fun a b => ?_⟩⟩` and prove the remaining obligations. Establish `e : adRep ((GG.map (algebraMap E (DualNumber E))).comp r) g (γ h) = (r g).mat.map (algebraMap E (DualNumber E)) * (if (r g).right = 1 then γ h else thetaLie (γ h)) * (((r g).left⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).map (algebraMap E (DualNumber E))` using `rfl`. Establish `e' : ∀ X, adRep r g X = (r g).mat * (if (r g).right = 1 then X else thetaLie X) * (((r g).left⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)` using `fun X => rfl`. Use `show (γ (g * h)).map _ = _`. Rewrite using `[hc g h, Matrix.map_add _ TrivSqZeroExt.snd_add, e, e', snd_mul_right, snd_mul_left]`.

Use `split_ifs`. Both sides reduce to the same expression. Unfold `thetaLie`. Rewrite using `[Matrix.map_neg _ TrivSqZeroExt.snd_neg, ← Jmat_map (algebraMap E (DualNumber E)), snd_mul_right, snd_mul_left]`. Both sides reduce to the same expression.

Use `TrivSqZeroExt.ext (h2 g a b) ?_` and prove the remaining obligations. Establish `e : (r' g).mat = (1 + γ g) * (r g).mat.map (algebraMap E (DualNumber E))` using `(hd g).2`. Establish `e2` using `congrArg (fun X : Matrix (Fin 3) (Fin 3) (DualNumber E) => X.map TrivSqZeroExt.snd a b) e`. Simplify using `only [snd_mul_right] at e2`. Use `e2.trans ?_` and prove the remaining obligations.

Use `show _ = ((γ g).map TrivSqZeroExt.snd * (r g).mat) a b`. Use `congrArg (fun X : Matrix (Fin 3) (Fin 3) E => (X * (r g).mat) a b) ?_` and prove the remaining obligations. Use extensionality with `c d`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem exists_coc {G E : Type} [Group G] [CommRing E] (r : G →* GG 3 E) (r' : G →* GG 3 (DualNumber E))
    (h1 : ∀ g, (r' g).right = (r g).right) (h2 : ∀ g a b, ((r' g).mat a b).fst = (r g).mat a b) :
    ∃ γ, IsCoc r γ ∧ DualDef r γ r' := by
  obtain ⟨γ, -, hc, hd⟩ := exists_isCoc (RingHom.ker (TrivSqZeroExt.fstHom E E E))
    ((GG.map (algebraMap E (DualNumber E))).comp r) r' (by
      rw [eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      have hx' : x.fst = 0 := hx
      have hy' : y.fst = 0 := hy
      rw [Ideal.mem_bot]
      ext <;> simp [hx', hy']) (MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => by
      refine Ideal.Quotient.eq.2 ?_
      show ((r' g).mat a b - algebraMap E (DualNumber E) ((r g).mat a b)).fst = 0
      simp [h2, TrivSqZeroExt.algebraMap_eq_inl])) (h1 g))
  refine ⟨fun g => (γ g).map TrivSqZeroExt.snd, fun g h => ?_, fun g => ⟨h1 g, fun a b => ?_⟩⟩
  · have e : adRep ((GG.map (algebraMap E (DualNumber E))).comp r) g (γ h) =
        (r g).mat.map (algebraMap E (DualNumber E)) * (if (r g).right = 1 then γ h else thetaLie (γ h)) *
          (((r g).left⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).map (algebraMap E (DualNumber E)) := rfl
    have e' : ∀ X, adRep r g X = (r g).mat * (if (r g).right = 1 then X else thetaLie X) *
          (((r g).left⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) := fun X => rfl
    show (γ (g * h)).map _ = _
    rw [hc g h, Matrix.map_add _ TrivSqZeroExt.snd_add, e, e', snd_mul_right, snd_mul_left]
    split_ifs
    · rfl
    · unfold thetaLie
      rw [Matrix.map_neg _ TrivSqZeroExt.snd_neg, ← Jmat_map (algebraMap E (DualNumber E)), snd_mul_right, snd_mul_left]
      rfl
  · refine TrivSqZeroExt.ext (h2 g a b) ?_
    have e : (r' g).mat = (1 + γ g) * (r g).mat.map (algebraMap E (DualNumber E)) := (hd g).2
    have e2 := congrArg (fun X : Matrix (Fin 3) (Fin 3) (DualNumber E) => X.map TrivSqZeroExt.snd a b) e
    simp only [snd_mul_right] at e2
    refine e2.trans ?_
    show _ = ((γ g).map TrivSqZeroExt.snd * (r g).mat) a b
    refine congrArg (fun X : Matrix (Fin 3) (Fin 3) E => (X * (r g).mat) a b) ?_
    ext c d
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply]
    split_ifs <;> simp

/- English proof (translation)
Introduce `hP l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ _ x hx n w φ u hφ hg hu j`. Use `letI : TopologicalSpace E := moduleTopology ℚ_[l] E`. Use `haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩`. Use `haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E`. Establish `hxe : ∀ g a b, algebraMap O E (x ((U.r.hom g).mat a b)) = (D.rz E g).mat a b` using `fun g a b => congrArg (fun r : GQ l →* GG 3 O => algebraMap O E ((r g).mat a b)) hx`.

Set `d : GQ l → Fin 3 → E` to `fun g b => algebraMap O E ((D.Ψ g ^ wt1 b : Oˣ) : O)`. Establish `hd : ∀ g, (D.rz E g).mat = Matrix.diagonal (d g)` using `fun g => Matrix.diagonal_map (map_zero (algebraMap O E))`. Establish `hdd : ∀ g b, d g b * d g⁻¹ b = 1` using `fun g b => by`. Simplify using `only [d]`. Rewrite using `[← map_mul, ← Units.val_mul, ← mul_zpow, ← map_mul]`.

Simplify using the standard rewrite rules. Establish `hdc : ∀ b, Continuous fun g => d g b` using `fun b => by`. Use `(ptCont (l := l) U.R E ((Algebra.ofId O E).comp x)).1 _ _ (U.r.cont b b)` as an intermediate fact. Use `Continuous.congr this fun g => (hxe g b b).trans ?_` and prove the remaining obligations. Rewrite using `[hd, Matrix.diagonal_apply_eq]`.

Establish `key : ∀ i, ∃ γ ∈ finiteCocycles (MonoidHom.id _) (adRep (D.rz E)), ∀ g a b, γ g a b = MvPowerSeries.coeff (Finsupp.single i 1) (φ ((U.r.hom g).mat a b)) * d g⁻¹ b` using `fun i => by`. Set `F : U.R →ₐ[O] DualNumber E` to `((jet i).restrictScalars O).comp φ`. Take `⟨γ, hc, hγ⟩` from `exists_coc (D.rz E) (push F U.r.hom) (fun g => U.r.hasMult g) (fun g a b => (hφ.const _).trans (hxe g a b))`. Establish `he : ∀ g a b, γ g a b = (F ((U.r.hom g).mat a b)).snd * d g⁻¹ b` using `fun g a b => by`. Establish `: (F ((U.r.hom g).mat a b)).snd = (γ g * (D.rz E g).mat) a b` using `congrArg TrivSqZeroExt.snd ((hγ g).2 a b)`.

Rewrite using `[this, hd, Matrix.mul_diagonal, mul_assoc, hdd, mul_one]`. Use `⟨γ, (rtTangent hP D U E γ ⟨?_, hc⟩ _ hγ).1 ⟨F, rfl, fun y hy => ?_⟩, he⟩` and prove the remaining obligations. Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [he]`. Use `Continuous.mul ?_ ((hdc b).comp continuous_inv)` and prove the remaining obligations.

Use `haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))`. Establish `hq` using `(ptCont (l := l) U.R (DualNumber E) F).1 _ _ (U.r.cont a b)`. Use `letI : TopologicalSpace (DualNumber E) := moduleTopology ℚ_[l] _`. Use `haveI : IsModuleTopology ℚ_[l] (DualNumber E) := ⟨rfl⟩`. Conclude with `(IsModuleTopology.continuous_of_linearMap ((TrivSqZeroExt.sndHom E E).restrictScalars ℚ_[l])).comp hq`.

Rewrite using `[← hφ.ker, RingHom.mem_ker] at hy show jet i (φ y) = 0`. Rewrite using `[hy, map_zero]`. Use `choose γ hγ he using key`. Take `⟨hfin, hdim, -⟩` from `dim_Z1f_crystalline_deformation hP D E j`. Use `haveI : Module.Finite E ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j) := Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)`.

Set `v : {i // w i = j} → ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j)` to `fun i => ⟨γ i, hγ i, fun g _ a b hab => by`. Rewrite using `[he, hg g a b _ (by`. Rewrite using `[Finsupp.weight_single, one_smul, i.2]`. Conclude with `hab.symm), zero_mul]⟩`. Establish `hv : LinearIndependent E v`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc k`. Establish `h1` using `congrArg (fun y : ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j) => y.1 (u k).1 (u k).2.1 (u k).2.2 * d (u k).1 (u k).2.2) hc`. Simplify using `only [v, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, he, hu, smul_eq_mul, Subtype.val_inj] at h1`. Simplify `h1` using `[mul_assoc, mul_comm (d (u k).1⁻¹ _), hdd]`.

Rewrite using `[← hdim, Nat.card_eq_fintype_card]`. Conclude with `hv.fintype_card_le_finrank`.
-/
theorem UpperTheory.V.Loc.chartCount :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (x : U.R →ₐ[O] O), IsBase D.η D.Ψ U.r.hom x → ∀ (n : ℕ) (w : Fin n → ℤ) (φ : U.R →ₐ[O] MvPowerSeries (Fin n) E) (u : Fin n → GQ l × Fin 3 × Fin 3), UpperTheory.V.Loc.IsCompl (D.It U) x φ → (∀ g a b, φ ((U.r.hom g).mat a b) ∈ wtPart E w (wt a b)) → (∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (φ ((U.r.hom (u i).1).mat (u i).2.1 (u i).2.2)) = if i = j then 1 else 0) → ∀ j, Nat.card {i // w i = j} ≤ locDims j := by
  intro hP l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ _ x hx n w φ u hφ hg hu j
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  have hxe : ∀ g a b, algebraMap O E (x ((U.r.hom g).mat a b)) = (D.rz E g).mat a b := fun g a b =>
    congrArg (fun r : GQ l →* GG 3 O => algebraMap O E ((r g).mat a b)) hx
  let d : GQ l → Fin 3 → E := fun g b => algebraMap O E ((D.Ψ g ^ wt1 b : Oˣ) : O)
  have hd : ∀ g, (D.rz E g).mat = Matrix.diagonal (d g) := fun g =>
    Matrix.diagonal_map (map_zero (algebraMap O E))
  have hdd : ∀ g b, d g b * d g⁻¹ b = 1 := fun g b => by
    simp only [d]
    rw [← map_mul, ← Units.val_mul, ← mul_zpow, ← map_mul]
    simp
  have hdc : ∀ b, Continuous fun g => d g b := fun b => by
    have := (ptCont (l := l) U.R E ((Algebra.ofId O E).comp x)).1 _ _ (U.r.cont b b)
    refine Continuous.congr this fun g => (hxe g b b).trans ?_
    rw [hd, Matrix.diagonal_apply_eq]
  have key : ∀ i, ∃ γ ∈ finiteCocycles (MonoidHom.id _) (adRep (D.rz E)), ∀ g a b,
      γ g a b = MvPowerSeries.coeff (Finsupp.single i 1) (φ ((U.r.hom g).mat a b)) * d g⁻¹ b := fun i => by
    let F : U.R →ₐ[O] DualNumber E := ((jet i).restrictScalars O).comp φ
    obtain ⟨γ, hc, hγ⟩ := exists_coc (D.rz E) (push F U.r.hom) (fun g => U.r.hasMult g)
      (fun g a b => (hφ.const _).trans (hxe g a b))
    have he : ∀ g a b, γ g a b = (F ((U.r.hom g).mat a b)).snd * d g⁻¹ b := fun g a b => by
      have : (F ((U.r.hom g).mat a b)).snd = (γ g * (D.rz E g).mat) a b :=
        congrArg TrivSqZeroExt.snd ((hγ g).2 a b)
      rw [this, hd, Matrix.mul_diagonal, mul_assoc, hdd, mul_one]
    refine ⟨γ, (rtTangent hP D U E γ ⟨?_, hc⟩ _ hγ).1 ⟨F, rfl, fun y hy => ?_⟩, he⟩
    · refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [he]
      refine Continuous.mul ?_ ((hdc b).comp continuous_inv)
      haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))
      have hq := (ptCont (l := l) U.R (DualNumber E) F).1 _ _ (U.r.cont a b)
      letI : TopologicalSpace (DualNumber E) := moduleTopology ℚ_[l] _
      haveI : IsModuleTopology ℚ_[l] (DualNumber E) := ⟨rfl⟩
      exact (IsModuleTopology.continuous_of_linearMap
        ((TrivSqZeroExt.sndHom E E).restrictScalars ℚ_[l])).comp hq
    · rw [← hφ.ker, RingHom.mem_ker] at hy
      show jet i (φ y) = 0
      rw [hy, map_zero]
  choose γ hγ he using key
  obtain ⟨hfin, hdim, -⟩ := dim_Z1f_crystalline_deformation hP D E j
  haveI : Module.Finite E ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)
  let v : {i // w i = j} → ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j) :=
    fun i => ⟨γ i, hγ i, fun g _ a b hab => by
      rw [he, hg g a b _ (by
        rw [Finsupp.weight_single, one_smul, i.2]
        exact hab.symm), zero_mul]⟩
  have hv : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h1 := congrArg (fun y : ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j) =>
      y.1 (u k).1 (u k).2.1 (u k).2.2 * d (u k).1 (u k).2.2) hc
    simp only [v, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply,
      Matrix.smul_apply, he, hu, smul_eq_mul, Subtype.val_inj] at h1
    simpa [mul_assoc, mul_comm (d (u k).1⁻¹ _), hdd] using h1
  rw [← hdim, Nat.card_eq_fintype_card]
  exact hv.fintype_card_le_finrank
