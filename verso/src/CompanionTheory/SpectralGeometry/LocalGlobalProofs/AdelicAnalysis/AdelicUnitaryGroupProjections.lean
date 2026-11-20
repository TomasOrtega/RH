import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HProj

section Alg

variable {F : Type} (E : Type) [Field F] [Field E] [Algebra F E]
  {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R''] [Algebra F R'']

def tm (φ : R →ₐ[F] R') : R ⊗[F] E →+* R' ⊗[F] E :=
  (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e => simp [tm]`. Consider the case `add x y hx hy => simp [hx, hy]`.
-/
theorem tm_comp (φ : R →ₐ[F] R') (ψ : R' →ₐ[F] R'') (x : R ⊗[F] E) :
    tm E (ψ.comp φ) x = tm E ψ (tm E φ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [tm]
  | add x y hx hy => simp [hx, hy]

variable {E}

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e => simp [tm, sigR]`. Consider the case `add x y hx hy => simp [hx, hy]`.
-/
theorem tm_sig (σ : E →ₐ[F] E) (φ : R →ₐ[F] R') (x : R ⊗[F] E) :
    tm E φ (sigR R σ x) = sigR R' σ (tm E φ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [tm, sigR]
  | add x y hx hy => simp [hx, hy]

/- English proof (translation)
Simplify using `[tm, inclR]`.
-/
theorem tm_incl (φ : R →ₐ[F] R') (e : E) : tm E φ (inclR R e) = inclR R' e := by
  simp [tm, inclR]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, hs]`.
-/
theorem map_cT {A B m p : Type} [CommRing A] [CommRing B] (f : A →+* B) (s : A →+* A) (s' : B →+* B)
    (hs : ∀ x, f (s x) = s' (f x)) (G : Matrix m p A) :
    (cT s G).map f = cT s' (G.map f) := by
  ext i j
  simp [cT, hs]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[JR, tm_incl]`.
-/
theorem map_JR {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] R') :
    (JR R J).map (tm E φ) = JR R' J := by
  ext i j
  simp [JR, tm_incl]

/- English proof (translation)
Rewrite using `[Matrix.map_mul, Matrix.map_mul, map_cT (tm E φ) (sigR R σ) (sigR R' σ) (tm_sig σ φ), map_JR]`.
-/
theorem map_unitary (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] R')
    (G : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :
    (cT (sigR R σ) G * JR R J * G).map (tm E φ) =
      cT (sigR R' σ) (G.map (tm E φ)) * JR R' J * G.map (tm E φ) := by
  rw [Matrix.map_mul, Matrix.map_mul, map_cT (tm E φ) (sigR R σ) (sigR R' σ) (tm_sig σ φ), map_JR]

def hMap (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] R') :
    HA R σ J →* HA R' σ J where
  toFun h := ⟨bc (tm E φ) (HA.mat R σ J h), by
    have hh : cT (sigR R σ) ((HA.mat R σ J h : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
        ((HA.mat R σ J h : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := (show HR R σ J from h).2
    have := congrArg (fun G => Matrix.map G (tm E φ)) hh
    simp only [map_unitary, map_JR] at this
    exact this⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (bc (tm E φ))
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul (bc (tm E φ)) _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hMap_mat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] R')
    (h : HA R σ J) :
    ((HA.mat R' σ J (hMap σ J φ h) : GL _ _) : Matrix (Fin M) (Fin M) (R' ⊗[F] E)) =
      ((HA.mat R σ J h : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (tm E φ) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_mul (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g h : HA R σ J) :
    HA.mat R σ J (g * h) = HA.mat R σ J g * HA.mat R σ J h := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_one (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    HA.mat R σ J 1 = 1 := rfl

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext e)`.
-/
theorem ha_ext (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {g h : HA R σ J}
    (e : ((HA.mat R σ J g : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = (HA.mat R σ J h : GL _ _)) :
    g = h :=
  Subtype.ext (Units.ext e)

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Simplify using `only [actW, actTup, hMap_mat, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]`.
-/
theorem tm_actW (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] R')
    (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    (fun a i => tm E φ (actW R σ J h X a i)) =
      actW R' σ J (hMap σ J φ h) (fun a i => tm E φ (X a i)) := by
  funext a i
  simp only [actW, actTup, hMap_mat, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

end Alg

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

def Lv (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v ⊗[F] E) :=
  {y | ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_latV {M n : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (Y : Fin n → Fin M → Fv F v ⊗[F] E) : Y ∈ latV b v ↔ ∀ a i, Y a i ∈ Lv b v := Iff.rfl

/- English proof (translation)
The claim follows from `(algebraMap F (Af F) c).2`.
-/
theorem ev_int (c : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      algebraMap F (Fv F v) c ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) c).2

/- English proof (translation)
Simplify using `[Algebra.TensorProduct.basis_repr_tmul]`.
-/
theorem repr_one_tmul (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr ((1 : Fv F v) ⊗ₜ[F] e) k =
      algebraMap F (Fv F v) (b.repr e k) := by
  simp [Algebra.TensorProduct.basis_repr_tmul]

/- English proof (translation)
Introduce `k`. Simplify using the standard rewrite rules.
-/
theorem Lv_zero (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : (0 : Fv F v ⊗[F] E) ∈ Lv b v := by
  intro k
  simp

/- English proof (translation)
Introduce `k`. Simplify using `only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]`. Conclude with `sum_mem fun i hi => hf i hi k`.
-/
theorem Lv_sum (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι)
    (f : ι → Fv F v ⊗[F] E) (hf : ∀ i ∈ s, f i ∈ Lv b v) : ∑ i ∈ s, f i ∈ Lv b v := by
  intro k
  simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  exact sum_mem fun i hi => hf i hi k

/- English proof (translation)
Establish `hc : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F` using `Filter.eventually_all.2 fun k => ev_int _`. Use `filter_upwards [hc] with v hv k`. Rewrite using `[Algebra.TensorProduct.one_def, repr_one_tmul]`. Conclude with `hv k`.
-/
theorem eventually_one (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (1 : Fv F v ⊗[F] E) ∈ Lv b v := by
  have hc : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k,
      algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => ev_int _
  filter_upwards [hc] with v hv k
  rw [Algebra.TensorProduct.one_def, repr_one_tmul]
  exact hv k

/- English proof (translation)
Establish `hc : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k l m, algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ v.adicCompletionIntegers F` using `Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => Filter.eventually_all.2 fun m => ev_int _`. Use `filter_upwards [hc] with v hv y z hy hz m`. Establish `hyz : y * z = ∑ k, ∑ l, ((Algebra.TensorProduct.basis (Fv F v) b).repr y k * (Algebra.TensorProduct.basis (Fv F v) b).repr z l) • ((1 : Fv F v) ⊗ₜ[F] (b k * b l))` using `by conv_lhs =>`. Rewrite using `[← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y, ← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]`. Rewrite using `[Finset.sum_mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_smul_comm, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite using `[hyz]`. Simplify using `only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_smul, Finsupp.smul_apply, repr_one_tmul, smul_eq_mul]`. Conclude with `sum_mem fun k _ => sum_mem fun l _ => mul_mem (mul_mem (hy k) (hz l)) (hv k l m)`.
-/
theorem eventually_mul (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ y z : Fv F v ⊗[F] E, y ∈ Lv b v → z ∈ Lv b v → y * z ∈ Lv b v := by
  have hc : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k l m,
      algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l =>
      Filter.eventually_all.2 fun m => ev_int _
  filter_upwards [hc] with v hv y z hy hz m
  have hyz : y * z = ∑ k, ∑ l,
      ((Algebra.TensorProduct.basis (Fv F v) b).repr y k *
        (Algebra.TensorProduct.basis (Fv F v) b).repr z l) • ((1 : Fv F v) ⊗ₜ[F] (b k * b l)) := by
    conv_lhs =>
      rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y,
        ← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hyz]
  simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_smul, Finsupp.smul_apply,
    repr_one_tmul, smul_eq_mul]
  exact sum_mem fun k _ => sum_mem fun l _ => mul_mem (mul_mem (hy k) (hz l)) (hv k l m)

/- English proof (translation)
Use `(mem_latV b v _).2 fun a i => ?_` and prove the remaining obligations. Establish `e : G.mulVec (X a) i = ∑ j, G i j * X a j` using `by simp [Matrix.mulVec, dotProduct]`. Use `show G.mulVec (X a) i ∈ Lv b v`. Rewrite using `[e]`. Conclude with `Lv_sum b v Finset.univ (fun j => G i j * X a j) fun j _ => hm _ _ (hG i j) ((mem_latV b v X).1 hX a j)`.
-/
theorem act_mem {M n : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (hm : ∀ y z : Fv F v ⊗[F] E, y ∈ Lv b v → z ∈ Lv b v → y * z ∈ Lv b v)
    (G : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) (hG : ∀ i j, G i j ∈ Lv b v)
    (X : Fin n → Fin M → Fv F v ⊗[F] E) (hX : X ∈ latV b v) :
    (fun a => G.mulVec (X a)) ∈ latV b v := by
  refine (mem_latV b v _).2 fun a i => ?_
  have e : G.mulVec (X a) i = ∑ j, G i j * X a j := by simp [Matrix.mulVec, dotProduct]
  show G.mulVec (X a) i ∈ Lv b v
  rw [e]
  exact Lv_sum b v Finset.univ (fun j => G i j * X a j) fun j _ =>
    hm _ _ (hG i j) ((mem_latV b v X).1 hX a j)

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [actW, actTup, Matrix.mulVec_mulVec]`. Rewrite using `[← Units.val_mul, ← mat_mul, inv_mul_cancel, mat_one, Units.val_one, Matrix.one_mulVec]`.
-/
theorem act_inv (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (g : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ J g⁻¹ (actW R σ J g X) = X := by
  funext a
  simp only [actW, actTup, Matrix.mulVec_mulVec]
  rw [← Units.val_mul, ← mat_mul, inv_mul_cancel, mat_one, Units.val_one, Matrix.one_mulVec]

abbrev evA (v : HeightOneSpectrum (𝓞 F)) : AF F →ₐ[F] Fv F v := (evalV F v).comp (sndA F)

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Conclude with `(tm_comp E (sndA F) (evalV F v) (X a i)).symm`.
-/
theorem projV_projFin {M n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → AF F ⊗[F] E) :
    projV v (projFin X) = fun a i => tm E (evA v) (X a i) := by
  funext a i
  exact (tm_comp E (sndA F) (evalV F v) (X a i)).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[Matrix.map_mul, hA, hA', Matrix.map_one (tm E φ) (map_zero _) (map_one _), ← Units.val_mul, ← mat_mul, mul_inv_cancel, mat_one, Units.val_one]`. Rewrite using `[map_unitary, hA, map_JR]`. Conclude with `(show HR R' σ J from g).2`.
-/
theorem map_eqs {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] R')
    (A A' : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (g : HA R' σ J)
    (hA : A.map (tm E φ) = ((HA.mat R' σ J g : GL _ _) : Matrix (Fin M) (Fin M) (R' ⊗[F] E)))
    (hA' : A'.map (tm E φ) = ((HA.mat R' σ J g⁻¹ : GL _ _) : Matrix (Fin M) (Fin M) (R' ⊗[F] E))) :
    (A * A').map (tm E φ) = (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (tm E φ) ∧
      (cT (sigR R σ) A * JR R J * A).map (tm E φ) = (JR R J).map (tm E φ) := by
  constructor
  · rw [Matrix.map_mul, hA, hA', Matrix.map_one (tm E φ) (map_zero _) (map_one _), ← Units.val_mul,
      ← mat_mul, mul_inv_cancel, mat_one, Units.val_one]
  · rw [map_unitary, hA, map_JR]
    exact (show HR R' σ J from g).2

end Lat

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J _`. Use `⟨hMap σ J (fstA F), fun v => hMap σ J (evA v), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `n h X`. Use `⟨tm_actW σ J (fstA F) h X, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[projV_projFin, projV_projFin]`.

Conclude with `tm_actW σ J (evA v) h X`. Introduce `d b h`. Establish `entries : ∀ h : HA (AF F) σ J, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, ((HA.mat (Fv F v) σ J (hMap σ J (evA v) h) : GL _ _) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ Lv b v`. Introduce `h`. Take `⟨-, -, -, -, -, ev, -, -, -⟩` from `GlobalTheory.T.adelic_tuple_projections F E σ hCM d b M M`.

Use `filter_upwards [ev (projFin (fun a i => ((HA.mat (AF F) σ J h : GL _ _) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) a i))] with v hv i j`. Rewrite `hv` using `[projV_projFin]`. Conclude with `(mem_latV b v _).1 hv i j`. Use `filter_upwards [eventually_mul b, entries h, entries h⁻¹] with v hm h1 h2 n X`. Prove the components needed by the constructor for the conclusion.

Introduce `hX`. Rewrite using `[← act_inv (Fv F v) σ J (hMap σ J (evA v) h) X, ← map_inv]`. Conclude with `act_mem b v hm _ h2 _ hX`. Introduce `hX`. Conclude with `act_mem b v hm _ h1 _ hX`.

Introduce `S ginf g classical haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Take `⟨-, -, -, -, -, -, inj, glue, -⟩` from `GlobalTheory.T.adelic_tuple_projections F E σ hCM _ (Module.finBasis F E) M M`. Establish `injM : ∀ A B : Matrix (Fin M) (Fin M) (AF F ⊗[F] E), A.map (tm E (fstA F)) = B.map (tm E (fstA F)) → (∀ v : HeightOneSpectrum (𝓞 F), A.map (tm E (evA v)) = B.map (tm E (evA v))) → A = B`. Introduce `A B h1 h2`. Use `inj A B h1 fun v => ?_` and prove the remaining obligations.

Conclude with `(projV_projFin v A).trans ((h2 v).trans (projV_projFin v B).symm)`. Establish `oneLat : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (fun a i => (1 : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) a i) ∈ (latV (Module.finBasis F E) v : Set (Fin M → Fin M → Fv F v ⊗[F] E))` using `by filter_upwards [eventually_one (Module.finBasis F E)] with v hv`. Use `(mem_latV _ v _).2 fun a i => ?_` and prove the remaining obligations. Distinguish the cases in `e : a = i`. Substitute `e` using the available equality.

Simplify using `using hv`. Simplify `Lv_zero (Module.finBasis F E) v` using `[Matrix.one_apply_ne e]`. Establish `glueM : ∀ (ginf : HA (Ainf F) σ J) (G : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J), (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, G v = 1) → ∃ X : Matrix (Fin M) (Fin M) (AF F ⊗[F] E), X.map (tm E (fstA F)) = ((HA.mat (Ainf F) σ J ginf : GL _ _) : Matrix (Fin M) (Fin M …`. Introduce `ginf G hG`. Take `⟨X, hXi, hXv⟩` from `glue (fun a i => ((HA.mat (Ainf F) σ J ginf : GL _ _) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)) a i) (fun v a i => ((HA.mat (Fv F v) σ J (G v) : GL _ _) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) a i) (by filter_upwards [hG, oneLat] with v h1 h2`.

Rewrite using `[h1]`. Conclude with `h2)`. Conclude with `⟨X, hXi, fun v => (projV_projFin v X).symm.trans (hXv v)⟩`. Set `G : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J` to `fun v => if v ∈ S then g v else 1`. Establish `hS : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, G v = 1` using `by filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv`.

Conclude with `if_neg hv`. Take `⟨X, mi, mv⟩` from `glueM ginf G hS`. Take `⟨X', mi', mv'⟩` from `glueM ginf⁻¹ (fun v => (G v)⁻¹) (by filter_upwards [hS] with v hv`. Rewrite using `[hv, inv_one])`. Establish `e1 : X * X' = 1` using `injM _ _ (map_eqs σ J _ _ _ ginf mi mi').1 fun v => (map_eqs σ J _ _ _ (G v) (mv v) (mv' v)).1`.

Establish `e2 : cT (sigR (AF F) σ) X * JR (AF F) J * X = JR (AF F) J` using `injM _ _ (map_eqs σ J _ _ _ ginf mi mi').2 fun v => (map_eqs σ J _ _ _ (G v) (mv v) (mv' v)).2`. Set `hh : HA (AF F) σ J` to `(⟨⟨X, X', e1, mul_eq_one_comm.1 e1⟩, e2⟩ : HR (AF F) σ J)`. Use `⟨hh, ha_ext σ J mi, fun v hv => ha_ext σ J ?_, fun v hv => ha_ext σ J ?_⟩` and prove the remaining obligations. Establish `e : G v = g v` using `if_pos hv`. Establish `m` using `mv v`.

Rewrite `m` using `[e]`. Conclude with `m`. Establish `e : G v = 1` using `if_neg hv`. Establish `m` using `mv v`. Rewrite `m` using `[e]`.

Conclude with `m`.
-/
theorem components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ (pinf : HA (AF F) σ J →* HA (Ainf F) σ J) (p : ∀ v : HeightOneSpectrum (𝓞 F), HA (AF F) σ J →* HA (Fv F v) σ J), (∀ (n : ℕ) (h : HA (AF F) σ J) (X : (Fin n → Fin M → AF F ⊗[F] E)), projInf (actW (AF F) σ J h X) = actW (Ainf F) σ J (pinf h) (projInf X) ∧ ∀ v, projV v (projFin (actW (AF F) σ J h X)) = actW (Fv F v) σ J (p v h) (projV v (projFin X))) ∧ (∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (h : HA (AF F) σ J), ∀ᶠ v in Filter.cofinite, ∀ (n : ℕ) (X : (Fin n → Fin M → Fv F v ⊗[F] E)), actW (Fv F v) σ J (p v h) X ∈ latV b v ↔ X ∈ latV b v) ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (ginf : HA (Ainf F) σ J) (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J), ∃ h : HA (AF F) σ J, pinf h = ginf ∧ (∀ v ∈ S, p v h = g v) ∧ ∀ v, v ∉ S → p v h = 1 := by
  intro F E _ _ _ _ _ σ hCM M J _
  refine ⟨hMap σ J (fstA F), fun v => hMap σ J (evA v), ?_, ?_, ?_⟩
  · intro n h X
    refine ⟨tm_actW σ J (fstA F) h X, fun v => ?_⟩
    rw [projV_projFin, projV_projFin]
    exact tm_actW σ J (evA v) h X
  · intro d b h
    have entries : ∀ h : HA (AF F) σ J, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j,
        ((HA.mat (Fv F v) σ J (hMap σ J (evA v) h) : GL _ _) :
          Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ Lv b v := by
      intro h
      obtain ⟨-, -, -, -, -, ev, -, -, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hCM d b M M
      filter_upwards [ev (projFin (fun a i =>
        ((HA.mat (AF F) σ J h : GL _ _) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) a i))] with v hv i j
      rw [projV_projFin] at hv
      exact (mem_latV b v _).1 hv i j
    filter_upwards [eventually_mul b, entries h, entries h⁻¹] with v hm h1 h2 n X
    constructor
    · intro hX
      rw [← act_inv (Fv F v) σ J (hMap σ J (evA v) h) X, ← map_inv]
      exact act_mem b v hm _ h2 _ hX
    · intro hX
      exact act_mem b v hm _ h1 _ hX
  · intro S ginf g
    classical
    haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
    obtain ⟨-, -, -, -, -, -, inj, glue, -⟩ :=
      GlobalTheory.T.adelic_tuple_projections F E σ hCM _ (Module.finBasis F E) M M
    have injM : ∀ A B : Matrix (Fin M) (Fin M) (AF F ⊗[F] E),
        A.map (tm E (fstA F)) = B.map (tm E (fstA F)) →
        (∀ v : HeightOneSpectrum (𝓞 F), A.map (tm E (evA v)) = B.map (tm E (evA v))) → A = B := by
      intro A B h1 h2
      refine inj A B h1 fun v => ?_
      exact (projV_projFin v A).trans ((h2 v).trans (projV_projFin v B).symm)
    have oneLat : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        (fun a i => (1 : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) a i) ∈
          (latV (Module.finBasis F E) v : Set (Fin M → Fin M → Fv F v ⊗[F] E)) := by
      filter_upwards [eventually_one (Module.finBasis F E)] with v hv
      refine (mem_latV _ v _).2 fun a i => ?_
      by_cases e : a = i
      · subst e; simpa using hv
      · simpa [Matrix.one_apply_ne e] using Lv_zero (Module.finBasis F E) v
    have glueM : ∀ (ginf : HA (Ainf F) σ J) (G : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J),
        (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, G v = 1) →
        ∃ X : Matrix (Fin M) (Fin M) (AF F ⊗[F] E),
          X.map (tm E (fstA F)) =
            ((HA.mat (Ainf F) σ J ginf : GL _ _) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)) ∧
          ∀ v : HeightOneSpectrum (𝓞 F), X.map (tm E (evA v)) =
            ((HA.mat (Fv F v) σ J (G v) : GL _ _) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) := by
      intro ginf G hG
      obtain ⟨X, hXi, hXv⟩ := glue
        (fun a i => ((HA.mat (Ainf F) σ J ginf : GL _ _) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)) a i)
        (fun v a i => ((HA.mat (Fv F v) σ J (G v) : GL _ _) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) a i)
        (by
          filter_upwards [hG, oneLat] with v h1 h2
          rw [h1]
          exact h2)
      exact ⟨X, hXi, fun v => (projV_projFin v X).symm.trans (hXv v)⟩
    let G : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J := fun v => if v ∈ S then g v else 1
    have hS : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, G v = 1 := by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      exact if_neg hv
    obtain ⟨X, mi, mv⟩ := glueM ginf G hS
    obtain ⟨X', mi', mv'⟩ := glueM ginf⁻¹ (fun v => (G v)⁻¹) (by
      filter_upwards [hS] with v hv
      rw [hv, inv_one])
    have e1 : X * X' = 1 :=
      injM _ _ (map_eqs σ J _ _ _ ginf mi mi').1 fun v => (map_eqs σ J _ _ _ (G v) (mv v) (mv' v)).1
    have e2 : cT (sigR (AF F) σ) X * JR (AF F) J * X = JR (AF F) J :=
      injM _ _ (map_eqs σ J _ _ _ ginf mi mi').2 fun v => (map_eqs σ J _ _ _ (G v) (mv v) (mv' v)).2
    let hh : HA (AF F) σ J := (⟨⟨X, X', e1, mul_eq_one_comm.1 e1⟩, e2⟩ : HR (AF F) σ J)
    refine ⟨hh, ha_ext σ J mi, fun v hv => ha_ext σ J ?_, fun v hv => ha_ext σ J ?_⟩
    · have e : G v = g v := if_pos hv
      have m := mv v
      rw [e] at m
      exact m
    · have e : G v = 1 := if_neg hv
      have m := mv v
      rw [e] at m
      exact m

end GlobalTheory.CompanionTheory.SW.HProj
