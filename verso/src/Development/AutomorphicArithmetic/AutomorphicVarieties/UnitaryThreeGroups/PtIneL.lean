import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CommutingUpperTriangularDistinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

/- English proof (translation)
Use `forall_congr' fun a => forall_congr' fun b => imp_congr_left ?_` and prove the remaining obligations. Use `show _ ↔ (b : ℕ) < a`. Simplify using `only [wt, wt1]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem up_iff {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) :
    (∀ a b, wt a b < 0 → X a b = 0) ↔ X.BlockTriangular id := by
  refine forall_congr' fun a => forall_congr' fun b => imp_congr_left ?_
  show _ ↔ (b : ℕ) < a
  simp only [wt, wt1]
  omega

/- English proof (translation)
Rewrite using `[theta_val]`. Generalize the expression as in `((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = v`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]`.
-/
private theorem theta_entry {R : Type} [CommRing R] (u : GL (Fin 3) R) (a b : Fin 3) :
    (theta u : Matrix (Fin 3) (Fin 3) R) a b = ((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) b.rev a.rev := by
  rw [theta_val]
  generalize ((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = v
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

/- English proof (translation)
Break down `Int.units_eq_one_or s with rfl | rfl` into its components or cases. Rewrite using `[sgnAct_one]`. Conclude with `⟨hu, fun _ h => h⟩`. Rewrite using `[sgnAct_neg_one]`. Establish `hv : ∀ a b, wt a b < 0 → ((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b = 0`.

Rewrite `hu`, the goal using `[up_iff]`. Use `letI := u.invertible`. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hu`. Use `⟨fun a b hab => ?_, fun t ht a => ?_⟩` and prove the remaining obligations.

Rewrite using `[theta_entry]`. Use `hv _ _ ?_` and prove the remaining obligations. Apply the tactic sequence `have : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl`. Rewrite using `[this]` and apply the resulting hypothesis. Rewrite using `[theta_entry]`.

Establish `hd : ∀ i, ((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) i i * (u : Matrix (Fin 3) (Fin 3) R) i i = 1`. Introduce `i`. Establish `e` using `congrFun (congrFun (Units.inv_mul u) i) i`. Establish `u10` using `hu 1 0 (by decide)`. Establish `u20` using `hu 2 0 (by decide)`.

Establish `u21` using `hu 2 1 (by decide)`. Establish `v10` using `hv 1 0 (by decide)`. Establish `v20` using `hv 2 0 (by decide)`. Establish `v21` using `hv 2 1 (by decide)`. Generalize the expression as in `((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = v at *`.

Apply the tactic sequence `fin_cases i <;> simpa [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, v10, v20, v21] using e`. Establish `e` using `hd a.rev`. Rewrite `e` using `[ht]`. Apply the tactic sequence `have w : wt1 a.rev = -wt1 a := by fin_cases a <;> rfl`. Rewrite `e` using `[w, _root_.zpow_neg]`.

Conclude with `Units.mul_inv_eq_one.1 e`.
-/
private theorem sgn_up {R : Type} [Field R] (s : ℤˣ) (u : GL (Fin 3) R)
    (hu : ∀ a b, wt a b < 0 → (u : Matrix (Fin 3) (Fin 3) R) a b = 0) :
    (∀ a b, wt a b < 0 → (sgnAct 3 R s u : Matrix (Fin 3) (Fin 3) R) a b = 0) ∧
      ∀ t : Rˣ, (∀ a, (u : Matrix (Fin 3) (Fin 3) R) a a = ((t ^ wt1 a : Rˣ) : R)) →
        ∀ a, (sgnAct 3 R s u : Matrix (Fin 3) (Fin 3) R) a a = ((t ^ wt1 a : Rˣ) : R) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [sgnAct_one]
    exact ⟨hu, fun _ h => h⟩
  · rw [sgnAct_neg_one]
    have hv : ∀ a b, wt a b < 0 → ((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b = 0 := by
      rw [up_iff] at hu ⊢
      letI := u.invertible
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular hu
    refine ⟨fun a b hab => ?_, fun t ht a => ?_⟩
    · rw [theta_entry]
      refine hv _ _ ?_
      have : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
      rwa [this]
    · rw [theta_entry]
      have hd : ∀ i, ((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) i i *
          (u : Matrix (Fin 3) (Fin 3) R) i i = 1 := by
        intro i
        have e := congrFun (congrFun (Units.inv_mul u) i) i
        have u10 := hu 1 0 (by decide)
        have u20 := hu 2 0 (by decide)
        have u21 := hu 2 1 (by decide)
        have v10 := hv 1 0 (by decide)
        have v20 := hv 2 0 (by decide)
        have v21 := hv 2 1 (by decide)
        generalize ((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = v at *
        fin_cases i <;> simpa [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, v10, v20, v21] using e
      have e := hd a.rev
      rw [ht] at e
      have w : wt1 a.rev = -wt1 a := by fin_cases a <;> rfl
      rw [w, _root_.zpow_neg] at e
      exact Units.mul_inv_eq_one.1 e

/- English proof (translation)
Set `w : GG 3 R` to `SemidirectProduct.inr (r g).right`. Establish `hM : GG.ofGL (w * GG.ofGL h * (r g)⁻¹).left = w * GG.ofGL h * (r g)⁻¹` using `SemidirectProduct.ext rfl (by simp [w])`. Use `⟨(w * GG.ofGL h * (r g)⁻¹).left, fun s hs => ?_⟩` and prove the remaining obligations. Establish `e : conjBy (w * GG.ofGL h * (r g)⁻¹).left r s = w * conjBy h r (g⁻¹ * s * g) * w⁻¹` using `by show GG.ofGL _ * r s * (GG.ofGL _)⁻¹ = w * (GG.ofGL h * r (g⁻¹ * s * g) * (GG.ofGL h)⁻¹) * w⁻¹`. Rewrite using `[hM, map_mul, map_mul, map_inv]`.

Use `group`. Rewrite using `[e]`. Simplify using `[w]`.
-/
private theorem move {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (h : GL (Fin 3) R) (g : G) :
    ∃ M : GL (Fin 3) R, ∀ s, (r (g⁻¹ * s * g)).right = 1 →
      (conjBy M r s).left = sgnAct 3 R (r g).right (conjBy h r (g⁻¹ * s * g)).left := by
  let w : GG 3 R := SemidirectProduct.inr (r g).right
  have hM : GG.ofGL (w * GG.ofGL h * (r g)⁻¹).left = w * GG.ofGL h * (r g)⁻¹ :=
    SemidirectProduct.ext rfl (by simp [w])
  refine ⟨(w * GG.ofGL h * (r g)⁻¹).left, fun s hs => ?_⟩
  have e : conjBy (w * GG.ofGL h * (r g)⁻¹).left r s = w * conjBy h r (g⁻¹ * s * g) * w⁻¹ := by
    show GG.ofGL _ * r s * (GG.ofGL _)⁻¹ = w * (GG.ofGL h * r (g⁻¹ * s * g) * (GG.ofGL h)⁻¹) * w⁻¹
    rw [hM, map_mul, map_mul, map_inv]
    group
  rw [e]
  simp [w]

/- English proof (translation)
Establish `: (conjBy M r s).left = M * (r s).left * M⁻¹` using `by simp [conjBy, hs]`. Simplify using `only [GG.mat, this, Units.val_mul]`. Rewrite using `[Matrix.coe_units_inv, Matrix.charpoly_units_conj]`.
-/
private theorem charpoly_conj {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (M : GL (Fin 3) R) (s : G)
    (hs : (r s).right = 1) : (conjBy M r s).mat.charpoly = (r s).mat.charpoly := by
  have : (conjBy M r s).left = M * (r s).left * M⁻¹ := by simp [conjBy, hs]
  simp only [GG.mat, this, Units.val_mul]
  rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]

/- English proof (translation)
Introduce `hI Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ _ r h A hA`. Take `⟨A₀, -, hD, hIn, -, -, -, hc⟩` from `dat_loc D`. Take `⟨x, hxD, hxI⟩` from `hc A hA`. Take `⟨f, -, hf1, hf2⟩` from `h.loc`. Take `⟨⟨b, hb⟩, -⟩` from `@Loc.lemma2b hI.loc l _ c.O _ _ c.dvr _ _ c.fin (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1 D.loc U (PadicAlgCl l) _ _ _ (r.comp D.ι) ⟨f, hf2, hf1⟩`.

Take `⟨M, hM⟩` from `move r b⁻¹ x`. Establish `hη : ∀ s, D.η (x⁻¹ * s * x) = D.η s` using `fun s => by`. Simplify using `only [map_mul, map_inv, inv_mul_cancel_comm]`. Establish `hΨ : ∀ s, D.ΨQ (x⁻¹ * s * x) = D.ΨQ s` using `fun s => by`. Simplify using `only [map_mul, map_inv, inv_mul_cancel_comm]`.

Establish `key : ∀ s σ, D.ι σ = x⁻¹ * s * x → D.η s = 1 → (∀ a a', wt a a' < 0 → (conjBy M r s).mat a a' = 0) ∧ (σ ∈ Loc.Iq l → ∀ a, (conjBy M r s).mat a a = (r0 D.η D.ΨQ s).mat a a)`. Introduce `s σ hσ hs`. Establish `h1 : D.η (D.ι σ) = 1` using `by rw [hσ, hη, hs]`. Establish `e1` using `hM s (by rw [h.mult, hη, hs])`. Rewrite `e1` using `[← hσ]`.

Take `⟨k1, k2⟩` from `sgn_up (r x).right (conjBy b⁻¹ r (D.ι σ)).left (hb.tri σ h1)`. Rewrite `k1`, `k2` using `[← e1]`. Use `⟨k1, fun hσI a => ?_⟩` and prove the remaining obligations. Rewrite using `[show (r0 D.η D.ΨQ s).mat a a = ((D.ΨQ s ^ wt1 a : (PadicAlgCl l)ˣ) : PadicAlgCl l) by`. Simplify using `only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq]]`.

Use `k2 (D.ΨQ s) (fun a => (hb.ine σ hσI h1 a).trans ?_) a` and prove the remaining obligations. Rewrite using `[← hΨ, ← hσ]`. Conclude with `congrArg Units.val (map_zpow (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom) (D.Ψ (D.ι σ)) (wt1 a))`. Establish `kI : ∀ s ∈ Ine (F` using `ℚ) A, D.η s = 1 ∧ (∀ a a', wt a a' < 0 → (conjBy M r s).mat a a' = 0) ∧ ∀ a, (conjBy M r s).mat a a = (r0 D.η D.ΨQ s).mat a a := by`. Introduce `s hs`.

Use `(hxI s).1 hs` as an intermediate fact. Rewrite `this` using `[← hIn]`. Take `⟨σ, hσI, hσ⟩` from `this`. Establish `h1 : D.η s = 1` using `by rw [← hη, ← hσ]; exact D.η_unr σ hσI`. Conclude with `⟨h1, (key s σ hσ h1).1, (key s σ hσ h1).2 hσI⟩`.

Use `⟨fun s hs => ?_, M, fun s hs h1 => ?_, fun s hs => (kI s hs).2.2⟩` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `kI s hs`. Rewrite using `[← charpoly_conj r M s ((h.mult s).trans h1), Matrix.charpoly_of_upperTriangular _ ((up_iff _).1 h2), Matrix.charpoly_of_upperTriangular (r0 D.η D.ΨQ s).mat (Matrix.blockTriangular_diagonal _)]`. Simplify using `only [h3]`. Use `(hxD s).1 hs` as an intermediate fact.

Rewrite `this` using `[← hD]`. Take `⟨σ, hσ⟩` from `this`. Conclude with `(key s σ hσ h1).1`.
-/
theorem UpperTheory.V.U3.pt_inertia_above :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r),
      ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
        (∀ g ∈ Ine (F := ℚ) A, (r g).mat.charpoly = (r0 D.η D.ΨQ g).mat.charpoly) ∧
        ∃ M : GL (Fin 3) (PadicAlgCl l), (∀ g ∈ Dec (F := ℚ) A, D.η g = 1 → ∀ a b, wt a b < 0 → (conjBy M r g).mat a b = 0) ∧
          ∀ g ∈ Ine (F := ℚ) A, ∀ a, (conjBy M r g).mat a a = (r0 D.η D.ΨQ g).mat a a := by
  intro hI Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ _ r h A hA
  obtain ⟨A₀, -, hD, hIn, -, -, -, hc⟩ := dat_loc D
  obtain ⟨x, hxD, hxI⟩ := hc A hA
  obtain ⟨f, -, hf1, hf2⟩ := h.loc
  obtain ⟨⟨b, hb⟩, -⟩ := @Loc.lemma2b hI.loc l _ c.O _ _ c.dvr _ _ c.fin
    (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1 D.loc U (PadicAlgCl l) _ _ _ (r.comp D.ι) ⟨f, hf2, hf1⟩
  obtain ⟨M, hM⟩ := move r b⁻¹ x
  have hη : ∀ s, D.η (x⁻¹ * s * x) = D.η s := fun s => by
    simp only [map_mul, map_inv, inv_mul_cancel_comm]
  have hΨ : ∀ s, D.ΨQ (x⁻¹ * s * x) = D.ΨQ s := fun s => by
    simp only [map_mul, map_inv, inv_mul_cancel_comm]
  have key : ∀ s σ, D.ι σ = x⁻¹ * s * x → D.η s = 1 → (∀ a a', wt a a' < 0 → (conjBy M r s).mat a a' = 0) ∧
      (σ ∈ Loc.Iq l → ∀ a, (conjBy M r s).mat a a = (r0 D.η D.ΨQ s).mat a a) := by
    intro s σ hσ hs
    have h1 : D.η (D.ι σ) = 1 := by rw [hσ, hη, hs]
    have e1 := hM s (by rw [h.mult, hη, hs])
    rw [← hσ] at e1
    obtain ⟨k1, k2⟩ := sgn_up (r x).right (conjBy b⁻¹ r (D.ι σ)).left (hb.tri σ h1)
    rw [← e1] at k1 k2
    refine ⟨k1, fun hσI a => ?_⟩
    rw [show (r0 D.η D.ΨQ s).mat a a = ((D.ΨQ s ^ wt1 a : (PadicAlgCl l)ˣ) : PadicAlgCl l) by
      simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq]]
    refine k2 (D.ΨQ s) (fun a => (hb.ine σ hσI h1 a).trans ?_) a
    rw [← hΨ, ← hσ]
    exact congrArg Units.val (map_zpow (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom) (D.Ψ (D.ι σ)) (wt1 a))
  have kI : ∀ s ∈ Ine (F := ℚ) A, D.η s = 1 ∧ (∀ a a', wt a a' < 0 → (conjBy M r s).mat a a' = 0) ∧
      ∀ a, (conjBy M r s).mat a a = (r0 D.η D.ΨQ s).mat a a := by
    intro s hs
    have := (hxI s).1 hs
    rw [← hIn] at this
    obtain ⟨σ, hσI, hσ⟩ := this
    have h1 : D.η s = 1 := by rw [← hη, ← hσ]; exact D.η_unr σ hσI
    exact ⟨h1, (key s σ hσ h1).1, (key s σ hσ h1).2 hσI⟩
  refine ⟨fun s hs => ?_, M, fun s hs h1 => ?_, fun s hs => (kI s hs).2.2⟩
  · obtain ⟨h1, h2, h3⟩ := kI s hs
    rw [← charpoly_conj r M s ((h.mult s).trans h1), Matrix.charpoly_of_upperTriangular _ ((up_iff _).1 h2),
      Matrix.charpoly_of_upperTriangular (r0 D.η D.ΨQ s).mat (Matrix.blockTriangular_diagonal _)]
    simp only [h3]
  · have := (hxD s).1 hs
    rw [← hD] at this
    obtain ⟨σ, hσ⟩ := this
    exact (key s σ hσ h1).1
