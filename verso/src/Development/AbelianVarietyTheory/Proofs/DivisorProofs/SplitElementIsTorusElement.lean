import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

open Formalism.UG (cT)

namespace GlobalTheory.IdTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use `h.1` as an intermediate fact. Establish `hw : w.IsReal` using `IsTotallyReal.isReal w`. Express the relevant statement in the definitionally equal form `infEmb τ (evInf F w (archUnitF F c : AF F) ⊗ₜ[F] (1 : E)) = _`. Rewrite using `[infEmb_tmul, map_one, mul_one]`. Establish `e1` using `congrArg (fun p => p.1 ⟨w, hw⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (fun _ => Real.exp c, fun _ => (Real.exp c : ℂ)))`.

Simplify using `only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at e1`. Rewrite using `[← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]`. Conclude with `congrArg (fun x : ℝ => (x : ℂ)) e1`.
-/
theorem infEmb_archUnit (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (c : ℝ) :
    infEmb τ (compInf F E w (archUnit F E c : AF F ⊗[F] E)) = (Real.exp c : ℂ) := by
  have := h.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  change infEmb τ (evInf F w (archUnitF F c : AF F) ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul, map_one, mul_one]
  have e1 := congrArg (fun p => p.1 ⟨w, hw⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply
    (fun _ => Real.exp c, fun _ => (Real.exp c : ℂ)))
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at e1
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
  exact congrArg (fun x : ℝ => (x : ℂ)) e1

/- English proof (translation)
Use `set R0 : Matrix (Fin n) (Fin n) K := 1 - X * Q - Y * P with hR0`. Establish `hP : P * R0 = 0`. Rewrite using `[hR0, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPX, hPY]`. Simplify using the standard rewrite rules. Establish `hQ : Q * R0 = 0`.

Rewrite using `[hR0, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQX, hQY]`. Simplify using the standard rewrite rules. Establish `hA : A * R0.map τ = R0.map τ`. Use extensionality with `i j`. Use `congrFun (hz (fun k => R0 k j) (funext fun k => congrFun (congrFun hP k) j) (funext fun k => congrFun (congrFun hQ k) j)) i` as an intermediate fact.

Conclude with `this`. Establish `h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = R0.map τ + X.map τ * Q.map τ + Y.map τ * P.map τ`. Establish `e : (1 : Matrix (Fin n) (Fin n) K) = R0 + X * Q + Y * P` using `by rw [hR0]; abel`. Use `congrArg (Matrix.map · τ) e` as an intermediate fact. Rewrite `this` using `[Matrix.map_add _ (map_add τ), Matrix.map_add _ (map_add τ), Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero τ) (map_one τ)]`.

Conclude with `this`. Establish `h2 : R0.map τ = 1 - X.map τ * Q.map τ - Y.map τ * P.map τ`. Rewrite using `[h1]`. Normalize the expressions using the abelian group laws. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_add, Matrix.mul_add, hA, ← Matrix.mul_assoc, hX, ← Matrix.mul_assoc, hY]`. Use `_ = _ := by`. Rewrite using `[h2, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_one]`. Normalize the expressions using the abelian group laws.
-/
theorem eq_of_frame {n r : ℕ} {K : Type} [Field K] (τ : K →+* ℂ) {X Y : Matrix (Fin n) (Fin r) K}
    {P Q : Matrix (Fin r) (Fin n) K} (hPX : P * X = 0) (hPY : P * Y = 1) (hQX : Q * X = 1) (hQY : Q * Y = 0)
    {A : Matrix (Fin n) (Fin n) ℂ} {D D' : Matrix (Fin r) (Fin r) ℂ}
    (hX : A * X.map τ = X.map τ * D) (hY : A * Y.map τ = Y.map τ * D')
    (hz : ∀ z : Fin n → K, P *ᵥ z = 0 → Q *ᵥ z = 0 → A *ᵥ (fun i => τ (z i)) = fun i => τ (z i)) :
    A = 1 + X.map τ * (D - 1) * Q.map τ + Y.map τ * (D' - 1) * P.map τ := by
  set R0 : Matrix (Fin n) (Fin n) K := 1 - X * Q - Y * P with hR0
  have hP : P * R0 = 0 := by
    rw [hR0, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPX, hPY]; simp
  have hQ : Q * R0 = 0 := by
    rw [hR0, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQX, hQY]; simp
  have hA : A * R0.map τ = R0.map τ := by
    ext i j
    have := congrFun (hz (fun k => R0 k j) (funext fun k => congrFun (congrFun hP k) j)
      (funext fun k => congrFun (congrFun hQ k) j)) i
    exact this
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = R0.map τ + X.map τ * Q.map τ + Y.map τ * P.map τ := by
    have e : (1 : Matrix (Fin n) (Fin n) K) = R0 + X * Q + Y * P := by rw [hR0]; abel
    have := congrArg (Matrix.map · τ) e
    rw [Matrix.map_add _ (map_add τ), Matrix.map_add _ (map_add τ), Matrix.map_mul, Matrix.map_mul,
      Matrix.map_one _ (map_zero τ) (map_one τ)] at this
    exact this
  have h2 : R0.map τ = 1 - X.map τ * Q.map τ - Y.map τ * P.map τ := by
    rw [h1]; abel
  calc A = A * 1 := (Matrix.mul_one A).symm
    _ = R0.map τ + X.map τ * D * Q.map τ + Y.map τ * D' * P.map τ := by
      conv_lhs => rw [h1]
      rw [Matrix.mul_add, Matrix.mul_add, hA, ← Matrix.mul_assoc, hX, ← Matrix.mul_assoc, hY]
    _ = _ := by
      rw [h2, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_one]
      abel

/- English proof (translation)
Take `⟨hfin, harch⟩ : IsTorusElt σ J X Y (fun i => Real.exp (stepSum S u i)) a` from `ha`. Set `d : Fin r → (AF F ⊗[F] E)ˣ` to `fun k => archUnit F E (stepSum S u k)`. Establish `c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z)` using `fun Z => rfl`. Establish `c3 : ∀ Z : Matrix (Fin n) (Fin r) E, (cT (sigR (AF F) σ) (adMat F Z) * JR (F` using `F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) = adMat F (cT (σ : E →+* E) Z * J) := fun Z => by`. Rewrite using `[c1]`.

Simplify using `only [adMat, JR, Matrix.map_mul]`. Establish `c2 : ∀ Z Z' : Matrix (Fin n) (Fin r) E, (cT (sigR (AF F) σ) (adMat F Z) * JR (F` using `F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Z' = adMat F (cT (σ : E →+* E) Z * J * Z') := fun Z Z' => by`. Rewrite using `[c3]`. Simplify using `only [adMat, Matrix.map_mul]`. Establish `hsd : ∀ k, sigR (AF F) σ (d k).1 = (d k).1` using `fun k => congrArg ((archUnitF F (stepSum S u k) : AF F) ⊗ₜ[F] ·) (map_one σ)`.

Take `⟨m, hm, hX, hY, he⟩` from `exists_unit_torus (s := sigR (AF F) σ) (J := JR (F := F) (AF F) J) (X := adMat F X) (Y := adMat F Y) (fun a => by`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma h x))`.

Use the proof step `((c1 J).trans (congrArg (adMat F) (Matrix.ext fun i j => hJ.1 i j)))`. Use the proof step `((c2 X X).trans (hW.xx ▸ Matrix.map_zero _ (map_zero _))) ((c2 Y Y).trans (hW.yy ▸ Matrix.map_zero _ (map_zero _)))`. Use the proof step `((c2 X Y).trans (hW.xy ▸ Matrix.map_one _ (map_zero _) (map_one _))) d hsd`. Establish `key : a = ⟨m, hm⟩`. Use `ext_inf_fin σ J ?_ ?_` and prove the remaining obligations.

Use `GInf_ext σ J fun w => ?_` and prove the remaining obligations. Rewrite using `[projInfArch_projInf σ J w a, projInfArch_projInf σ J w (⟨m, hm⟩ : GAd σ J)]`. Take `⟨τ⟩ : Nonempty (EmbOver E w)` from `inferInstance`. Apply `(archEquiv J h τ).injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[← GlobalTheory.Orb.archMat_eq_archEquiv J h, ← GlobalTheory.Orb.archMat_eq_archEquiv J h]`. Take `⟨hA1, hA2, hA3⟩` from `harch w τ`. Rewrite using `[eq_of_frame τ.1 (P := cT (σ : E →+* E) X * J) (Q := cT (σ : E →+* E) Y * J) hW.xx hW.xy (yx h hJ hW) hW.yy hA1 hA2 hA3]`. Set `φ` to `(infEmb τ).comp (compInf F E w)`.

Establish `h0 : ∀ x : E, φ (inclR (F` using `F) (AF F) x) = τ.1 x := fun x => by`. Express the relevant statement in the definitionally equal form `infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _`. Simplify using the standard rewrite rules. Establish `h2 : ∀ {p q : ℕ} (Z : Matrix (Fin p) (Fin q) E), (adMat F Z).map φ = Z.map τ.1` using `fun Z => Matrix.ext fun i j => h0 _`. Establish `h3 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w ⟨m, hm⟩) = m.1.map φ` using `rfl`.

Establish `hd1 : ∀ k, φ (d k).1 = (Real.exp (stepSum S u k) : ℂ)` using `fun k => infEmb_archUnit h τ _`. Establish `hd2 : ∀ k, φ (d k)⁻¹.1 = (Real.exp (stepSum S u k) : ℂ)⁻¹` using `fun k => by`. Rewrite using `[map_units_inv φ (d k), hd1]`. Establish `hR : m.1.map φ = 1 + X.map τ.1 * diagonal (fun i => (Real.exp (stepSum S u i) : ℂ) - 1) * (cT (σ : E →+* E) Y * J).map τ.1 + Y.map τ.1 * diagonal (fun i => (Real.exp (stepSum S u i) : ℂ)⁻¹ - 1) * (cT (σ : E →+* E) X * J).map τ.1` using `by conv_lhs => rw [he, c3, c3, Matrix.map_add _ (map_add φ), Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero φ) (map_one φ), h2, h2, h2, h2, diagonal_map (map_zero φ), diagonal_map (map_zero φ)]`. Simplify using `only [map_sub, map_one, hd1, hd2]`.

Establish `hD : ∀ f : Fin r → ℂ, diagonal f - 1 = diagonal (fun i => f i - 1)` using `fun f => by`. Rewrite using `[← diagonal_one, diagonal_sub]`. Rewrite using `[h3, hR, hD, hD]`. Establish `e1 : projFin σ J a = 1` using `matHom_injective _ σ J (by rw [map_one]; exact MonoidHom.mem_ker.1 hfin)`. Establish `e2 : projFin σ J ⟨m, hm⟩ = 1` using `matHom_injective _ σ J (by`.

Rewrite using `[map_one]`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Set `ψ` to `(Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom`. Establish `h1 : ∀ k, ψ (d k).1 = 1` using `fun k => rfl`. Establish `h2 : ∀ k, ψ (d k)⁻¹.1 = 1` using `fun k => rfl`.

Express the relevant statement in the definitionally equal form `ψ (m.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j`. Rewrite using `[he]`. Simplify using `only [Matrix.add_apply, Matrix.mul_apply (N := cT _ _ * _), mul_diagonal, map_add, map_sum, map_mul, map_sub, h1, h2, map_one, sub_self, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.one_apply, apply_ite ψ, map_zero])`. Rewrite using `[e1, e2]`. Substitute `key` using the available equality.

Establish `hc : ∀ k, conjUnit σ (d k) = d k` using `fun k => Units.ext (hsd k)`. Establish `hperp : ∀ (Z : Matrix (Fin n) (Fin r) E) (z : Fin n → AF F ⊗[F] E), z ∈ colPerp σ J Z Set.univ → (cT (sigR (AF F) σ) (adMat F Z) * JR (F` using `F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *ᵥ z = 0 := fun Z z hz => by`. Rewrite using `[c3]`. Use function extensionality and compare the values at `i`. Use `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hz i) (Set.mem_univ i)` as an intermediate fact.

Conclude with `LinearMap.mem_ker.1 this`. Use `⟨hX, ?_, fun z hz => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `m.1 * adMat F Y = adMat F Y * diagonal (fun k => (((conjUnit σ (d k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E))`. Simplify using `only [hc]`. Conclude with `hY`.

Express the relevant statement in the definitionally equal form `m.1 *ᵥ z = z`. Rewrite using `[he, add_mulVec, add_mulVec, ← mulVec_mulVec, hperp Y z hz.2, mulVec_zero, ← mulVec_mulVec, hperp X z hz.1]`. Simplify using the standard rewrite rules.
-/
theorem isIdTorusElt_of_isSplitElt {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (S : Finset (Fin r)) (u : Fin r → ℝ)
    {a : GAd σ J} (ha : IsSplitElt σ J X Y S u a) :
    IsIdTorusElt σ J X Y (fun k => archUnit F E (stepSum S u k)) a := by
  obtain ⟨hfin, harch⟩ : IsTorusElt σ J X Y (fun i => Real.exp (stepSum S u i)) a := ha
  let d : Fin r → (AF F ⊗[F] E)ˣ := fun k => archUnit F E (stepSum S u k)
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have c3 : ∀ Z : Matrix (Fin n) (Fin r) E, (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J :
      Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) = adMat F (cT (σ : E →+* E) Z * J) := fun Z => by
    rw [c1]; simp only [adMat, JR, Matrix.map_mul]
  have c2 : ∀ Z Z' : Matrix (Fin n) (Fin r) E, (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J :
      Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Z' = adMat F (cT (σ : E →+* E) Z * J * Z') := fun Z Z' => by
    rw [c3]; simp only [adMat, Matrix.map_mul]
  have hsd : ∀ k, sigR (AF F) σ (d k).1 = (d k).1 := fun k =>
    congrArg ((archUnitF F (stepSum S u k) : AF F) ⊗ₜ[F] ·) (map_one σ)
  obtain ⟨m, hm, hX, hY, he⟩ := exists_unit_torus (s := sigR (AF F) σ) (J := JR (F := F) (AF F) J) (X := adMat F X)
    (Y := adMat F Y)
    (fun a => by
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma h x))
    ((c1 J).trans (congrArg (adMat F) (Matrix.ext fun i j => hJ.1 i j)))
    ((c2 X X).trans (hW.xx ▸ Matrix.map_zero _ (map_zero _))) ((c2 Y Y).trans (hW.yy ▸ Matrix.map_zero _ (map_zero _)))
    ((c2 X Y).trans (hW.xy ▸ Matrix.map_one _ (map_zero _) (map_one _))) d hsd
  have key : a = ⟨m, hm⟩ := by
    refine ext_inf_fin σ J ?_ ?_
    · refine GInf_ext σ J fun w => ?_
      rw [projInfArch_projInf σ J w a, projInfArch_projInf σ J w (⟨m, hm⟩ : GAd σ J)]
      obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
      apply (archEquiv J h τ).injective
      apply Subtype.ext
      apply Units.ext
      rw [← GlobalTheory.Orb.archMat_eq_archEquiv J h, ← GlobalTheory.Orb.archMat_eq_archEquiv J h]
      obtain ⟨hA1, hA2, hA3⟩ := harch w τ
      rw [eq_of_frame τ.1 (P := cT (σ : E →+* E) X * J) (Q := cT (σ : E →+* E) Y * J) hW.xx hW.xy (yx h hJ hW) hW.yy
        hA1 hA2 hA3]
      let φ := (infEmb τ).comp (compInf F E w)
      have h0 : ∀ x : E, φ (inclR (F := F) (AF F) x) = τ.1 x := fun x => by
        change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
        simp
      have h2 : ∀ {p q : ℕ} (Z : Matrix (Fin p) (Fin q) E), (adMat F Z).map φ = Z.map τ.1 := fun Z =>
        Matrix.ext fun i j => h0 _
      have h3 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w ⟨m, hm⟩) = m.1.map φ := rfl
      have hd1 : ∀ k, φ (d k).1 = (Real.exp (stepSum S u k) : ℂ) := fun k => infEmb_archUnit h τ _
      have hd2 : ∀ k, φ (d k)⁻¹.1 = (Real.exp (stepSum S u k) : ℂ)⁻¹ := fun k => by
        rw [map_units_inv φ (d k), hd1]
      have hR : m.1.map φ = 1 + X.map τ.1 * diagonal (fun i => (Real.exp (stepSum S u i) : ℂ) - 1) *
          (cT (σ : E →+* E) Y * J).map τ.1 +
          Y.map τ.1 * diagonal (fun i => (Real.exp (stepSum S u i) : ℂ)⁻¹ - 1) * (cT (σ : E →+* E) X * J).map τ.1 := by
        conv_lhs => rw [he, c3, c3, Matrix.map_add _ (map_add φ), Matrix.map_add _ (map_add φ), Matrix.map_mul,
          Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero φ) (map_one φ), h2, h2, h2, h2,
          diagonal_map (map_zero φ), diagonal_map (map_zero φ)]
        simp only [map_sub, map_one, hd1, hd2]
      have hD : ∀ f : Fin r → ℂ, diagonal f - 1 = diagonal (fun i => f i - 1) := fun f => by
        rw [← diagonal_one, diagonal_sub]
      rw [h3, hR, hD, hD]
    · have e1 : projFin σ J a = 1 := matHom_injective _ σ J (by rw [map_one]; exact MonoidHom.mem_ker.1 hfin)
      have e2 : projFin σ J ⟨m, hm⟩ = 1 := matHom_injective _ σ J (by
        rw [map_one]
        refine Units.ext (Matrix.ext fun i j => ?_)
        let ψ := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
        have h1 : ∀ k, ψ (d k).1 = 1 := fun k => rfl
        have h2 : ∀ k, ψ (d k)⁻¹.1 = 1 := fun k => rfl
        change ψ (m.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j
        rw [he]
        simp only [Matrix.add_apply, Matrix.mul_apply (N := cT _ _ * _), mul_diagonal, map_add, map_sum, map_mul, map_sub,
          h1, h2, map_one, sub_self, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.one_apply, apply_ite ψ,
          map_zero])
      rw [e1, e2]
  subst key
  have hc : ∀ k, conjUnit σ (d k) = d k := fun k => Units.ext (hsd k)
  have hperp : ∀ (Z : Matrix (Fin n) (Fin r) E) (z : Fin n → AF F ⊗[F] E), z ∈ colPerp σ J Z Set.univ →
      (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *ᵥ z = 0 :=
    fun Z z hz => by
      rw [c3]
      funext i
      have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hz i) (Set.mem_univ i)
      exact LinearMap.mem_ker.1 this
  refine ⟨hX, ?_, fun z hz => ?_⟩
  · change m.1 * adMat F Y = adMat F Y * diagonal (fun k => (((conjUnit σ (d k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E))
    simp only [hc]
    exact hY
  · change m.1 *ᵥ z = z
    rw [he, add_mulVec, add_mulVec, ← mulVec_mulVec, hperp Y z hz.2, mulVec_zero, ← mulVec_mulVec, hperp X z hz.1]
    simp

end GlobalTheory.IdTorus
