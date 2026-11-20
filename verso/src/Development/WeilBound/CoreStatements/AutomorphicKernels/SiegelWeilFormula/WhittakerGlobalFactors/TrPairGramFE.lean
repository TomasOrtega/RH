import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MeasurableSetUH

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Tens

variable {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R''] [Algebra F R'']

abbrev fE (f : R →ₐ[F] R') : R ⊗[F] E →ₐ[F] R' ⊗[F] E := Algebra.TensorProduct.map f (AlgHom.id F E)

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [fE]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem fE_comp (f : R →ₐ[F] R') (g : R' →ₐ[F] R'') (x : R ⊗[F] E) :
    fE (E := E) g (fE f x) = fE (g.comp f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [fE]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Simplify using `[fE, inclR]`.
-/
theorem fE_inclR (f : R →ₐ[F] R') (e : E) : fE f (inclR R e) = inclR R' e := by
  simp [fE, inclR]

/- English proof (translation)
Establish `h1` using `GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.trace_map (AlgHom.id F R) bs x`. Establish `h2` using `GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.trace_map f bs x`. Establish `h3 : Algebra.TensorProduct.map (AlgHom.id F R) (AlgHom.id F E) x = x`. Rewrite using `[Algebra.TensorProduct.map_id]`. Both sides reduce to the same expression.

Rewrite `h1` using `[h3]`. Rewrite using `[fE, h2, h1, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, AlgHom.commutes]`. Both sides reduce to the same expression.
-/
theorem trace_fE {d : ℕ} (bs : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') (x : R ⊗[F] E) :
    f (Algebra.trace R (R ⊗[F] E) x) = Algebra.trace R' (R' ⊗[F] E) (fE f x) := by
  have h1 := GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.trace_map (AlgHom.id F R) bs x
  have h2 := GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.trace_map f bs x
  have h3 : Algebra.TensorProduct.map (AlgHom.id F R) (AlgHom.id F E) x = x := by
    rw [Algebra.TensorProduct.map_id]; rfl
  rw [h3] at h1
  rw [fE, h2, h1, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, AlgHom.commutes]
  rfl

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.SiegelND.Coef.sigR_map f σ x`.
-/
theorem sigR_fE (σ : E →ₐ[F] E) (f : R →ₐ[F] R') (x : R ⊗[F] E) : sigR R' σ (fE f x) = fE f (sigR R σ x) :=
  GlobalTheory.CompanionTheory.SiegelND.Coef.sigR_map f σ x

/- English proof (translation)
Simplify using `only [trPair, map_mul, AlgHom.commutes]`. Rewrite using `[trace_fE bs]`. Simplify using `[map_sum, map_mul, Matrix.map_apply]`.
-/
theorem trPair_fE {d : ℕ} (bs : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) (R ⊗[F] E)) :
    f (trPair R A B) = trPair R' (A.map (fE f)) (B.map (fE f)) := by
  simp only [trPair, map_mul, AlgHom.commutes]
  rw [trace_fE bs]
  simp [map_sum, map_mul, Matrix.map_apply]

/- English proof (translation)
Use extensionality with `a c`. Simplify using `only [Matrix.map_apply, gramR, hR, hform, JR, Matrix.map_apply, map_sum, map_mul, sigR_fE, fE_inclR]`.
-/
theorem gramR_fE (σ : E →ₐ[F] E) (f : R →ₐ[F] R') {M m : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin m → Fin M → R ⊗[F] E) :
    (gramR R σ J Y).map (fE f) = gramR R' σ J (fun a i => fE f (Y a i)) := by
  ext a c
  simp only [Matrix.map_apply, gramR, hR, hform, JR, Matrix.map_apply, map_sum, map_mul, sigR_fE, fE_inclR]

/- English proof (translation)
Rewrite using `[trPair_fE bs, gramR_fE]`.
-/
theorem trPair_gram_fE {d : ℕ} (bs : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) (f : R →ₐ[F] R') {M m : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin m) (Fin m) (R ⊗[F] E)) (Y : Fin m → Fin M → R ⊗[F] E) :
    f (trPair R B (gramR R σ J Y)) = trPair R' (B.map (fE f)) (gramR R' σ J (fun a i => fE f (Y a i))) := by
  rw [trPair_fE bs, gramR_fE]

/- English proof (translation)
Rewrite using `[trPair_fE bs]`. Use `congr 1`. Use extensionality with `a c`. Simplify using `[Matrix.map_apply, fE_inclR]`.
-/
theorem trPair_T_fE {d : ℕ} (bs : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') {m : ℕ}
    (T : Matrix (Fin m) (Fin m) E) (B : Matrix (Fin m) (Fin m) (R ⊗[F] E)) :
    f (trPair R (T.map (inclR R)) B) = trPair R' (T.map (inclR R')) (B.map (fE f)) := by
  rw [trPair_fE bs]
  congr 1
  ext a c
  simp [Matrix.map_apply, fE_inclR]

end Tens

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hermInf_val (σ : E →ₐ[F] E) {n : ℕ} (b : HermR (AF F) σ n) :
    ((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = matInf (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
  rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [hermV, hermFin, GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap, matV, Matrix.map_apply]`. Conclude with `fE_comp (sndA F) (evalV F v) _`.
-/
theorem hermV_val (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (b : HermR (AF F) σ n) :
    ((hermV σ v (hermFin σ b) : HermR (Fv F v) σ n) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) =
      matV v (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) := by
  ext i j
  simp only [hermV, hermFin, GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap, matV, Matrix.map_apply]
  exact fE_comp (sndA F) (evalV F v) _

/- English proof (translation)
Rewrite using `[hermV_val]`. Both sides reduce to the same expression.
-/
theorem hermV_val' (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (b : HermR (AF F) σ n) :
    ((hermV σ v (hermFin σ b) : HermR (Fv F v) σ n) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) =
      (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (fE ((evalV F v).comp (sndA F))) := by
  rw [hermV_val]; rfl

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Conclude with `fE_comp (sndA F) (evalV F v) _`.
-/
theorem projV_projFin {M n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → AF F ⊗[F] E) :
    projV v (projFin X) = fun a i => fE ((evalV F v).comp (sndA F)) (X a i) := by
  funext a i
  exact fE_comp (sndA F) (evalV F v) _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem projInf_eq {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) :
    projInf X = fun a i => fE (fstA F) (X a i) := rfl

end PositivityTheory.SiegelWeilFormula.GFac

end
