import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LinearChangeEulerProductStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PfHerm

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

abbrev Idx (n d : ℕ) := Fin n ⊕ ({p : Fin n × Fin n // p.1 < p.2} × Fin d)

variable (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `tmul s e => simp [TensorProduct.smul_tmul', HaarCoord.sigR_tmul]`. Consider the case `add a b ha hb => simp only [smul_add, map_add, ha, hb]`.
-/
theorem sigR_smul (σ : E →ₐ[F] E) (r : R) (y : R ⊗[F] E) :
    sigR R σ (r • y) = r • sigR R σ y := by
  induction y with
  | zero => simp
  | tmul s e => simp [TensorProduct.smul_tmul', HaarCoord.sigR_tmul]
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]

variable {d n : ℕ}

def offE (b : Module.Basis (Fin d) F E) (x : Idx n d → R)
    (p : {p : Fin n × Fin n // p.1 < p.2}) : R ⊗[F] E :=
  ∑ k, x (Sum.inr (p, k)) ⊗ₜ[F] b k

def psi (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (x : Idx n d → R) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  HaarCoord.hermMat R σ n ((fun i => x (Sum.inl i)), offE R b x)

def coordOf (b : Module.Basis (Fin d) F E) (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : Idx n d → R :=
  Sum.elim (fun i => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (S i i))
    (fun q => (Algebra.TensorProduct.basis R b).repr (S q.1.1.1 q.1.1.2) q.2)

/- English proof (translation)
Simplify using `only [psi, HaarCoord.hermMat, dif_pos h]`.
-/
theorem psi_lt (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (x : Idx n d → R) {a c : Fin n}
    (h : a < c) : psi R σ b x a c = offE R b x ⟨(a, c), h⟩ := by
  simp only [psi, HaarCoord.hermMat, dif_pos h]

/- English proof (translation)
Simplify using `only [psi, HaarCoord.hermMat, dif_neg (not_lt_of_gt h), dif_pos h]`.
-/
theorem psi_gt (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (x : Idx n d → R) {a c : Fin n}
    (h : c < a) : psi R σ b x a c = sigR R σ (offE R b x ⟨(c, a), h⟩) := by
  simp only [psi, HaarCoord.hermMat, dif_neg (not_lt_of_gt h), dif_pos h]

/- English proof (translation)
Simplify using `only [psi, HaarCoord.hermMat, lt_irrefl, dite_false]`.
-/
theorem psi_eq (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (x : Idx n d → R) (a : Fin n) :
    psi R σ b x a a = x (Sum.inl a) ⊗ₜ[F] (1 : E) := by
  simp only [psi, HaarCoord.hermMat, lt_irrefl, dite_false]

/- English proof (translation)
Simplify using `[offE, TensorProduct.add_tmul, Finset.sum_add_distrib]`.
-/
theorem offE_add (b : Module.Basis (Fin d) F E) (x y : Idx n d → R) (p) :
    offE R b (x + y) p = offE R b x p + offE R b y p := by
  simp [offE, TensorProduct.add_tmul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[offE, Finset.smul_sum, TensorProduct.smul_tmul']`.
-/
theorem offE_smul (b : Module.Basis (Fin d) F E) (r : R) (x : Idx n d → R) (p) :
    offE R b (r • x) p = r • offE R b x p := by
  simp [offE, Finset.smul_sum, TensorProduct.smul_tmul']

def psiL (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) :
    (Idx n d → R) →ₗ[R] Matrix (Fin n) (Fin n) (R ⊗[F] E) where
  toFun := psi R σ b
  map_add' x y := by
    ext a c
    rcases lt_trichotomy a c with h | h | h
    · simp [psi_lt R σ b _ h, offE_add]
    · subst h
      simp [psi_eq, TensorProduct.add_tmul]
    · simp [psi_gt R σ b _ h, offE_add]
  map_smul' r x := by
    ext a c
    rcases lt_trichotomy a c with h | h | h
    · simp [psi_lt R σ b _ h, offE_smul]
    · subst h
      simp [psi_eq, TensorProduct.smul_tmul']
    · simp [psi_gt R σ b _ h, offE_smul, sigR_smul]

def coordL (b : Module.Basis (Fin d) F E) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) →ₗ[R] (Idx n d → R) where
  toFun := coordOf R b
  map_add' S T := by
    ext i
    rcases i with i | q <;> simp [coordOf, mul_add]
  map_smul' r S := by
    ext i
    rcases i with i | q
    · simp [coordOf]
      ring
    · simp [coordOf]

def mg (σ : E →ₐ[F] E) (G : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) →ₗ[R] Matrix (Fin n) (Fin n) (R ⊗[F] E) where
  toFun S := cT (sigR R σ) G * S * G
  map_add' S T := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' r S := by simp [Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
The claim follows from `HaarCoord.hermMat_mem R hinv n _`.
-/
theorem psi_mem {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) (b : Module.Basis (Fin d) F E)
    (x : Idx n d → R) : psi R σ b x ∈ HermR R σ n :=
  HaarCoord.hermMat_mem R hinv n _

/- English proof (translation)
Use extensionality with `i`. Break down `i with i | ⟨⟨⟨a, c⟩, h⟩, k⟩` into its components or cases. Simplify using `only [coordOf, Sum.elim_inl, psi_eq]`. Conclude with `HaarCoord.half_trace_tmul R h2 _`. Establish `h' : a < c` using `h`.

Simplify using `only [coordOf, Sum.elim_inr, psi_lt R σ b x h', offE]`. Establish `: (∑ k, x (Sum.inr (⟨(a, c), h⟩, k)) ⊗ₜ[F] b k) = ∑ k, x (Sum.inr (⟨(a, c), h⟩, k)) • Algebra.TensorProduct.basis R b k`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `[Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']`. Rewrite using `[this, Module.Basis.repr_sum_self]`.
-/
theorem coord_psi [CharZero F] (h2 : Module.finrank F E = 2) (σ : E →ₐ[F] E)
    (b : Module.Basis (Fin d) F E) (x : Idx n d → R) : coordOf R b (psi R σ b x) = x := by
  ext i
  rcases i with i | ⟨⟨⟨a, c⟩, h⟩, k⟩
  · simp only [coordOf, Sum.elim_inl, psi_eq]
    exact HaarCoord.half_trace_tmul R h2 _
  · have h' : a < c := h
    simp only [coordOf, Sum.elim_inr, psi_lt R σ b x h', offE]
    have : (∑ k, x (Sum.inr (⟨(a, c), h⟩, k)) ⊗ₜ[F] b k) =
        ∑ k, x (Sum.inr (⟨(a, c), h⟩, k)) • Algebra.TensorProduct.basis R b k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
    rw [this, Module.Basis.repr_sum_self]

/- English proof (translation)
Establish `hoff : ∀ p : {p : Fin n × Fin n // p.1 < p.2}, offE R b (coordOf R b S) p = S p.1.1 p.1.2`. Introduce `p`. Use `(Algebra.TensorProduct.basis R b).sum_repr (S p.1.1 p.1.2)` as an intermediate fact. Use `conv_rhs => rw [← this]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `[coordOf, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']`. Use extensionality with `a c`. Break down `lt_trichotomy a c with h | h | h` into its components or cases. Rewrite using `[psi_lt R σ b _ h, hoff]`. Substitute `h` using the available equality.

Take `⟨r, hr⟩` from `HaarCoord.fixed_eq_tmul R hinv h2 hδ hσδ (S a a) (hS a a)`. Rewrite using `[psi_eq]`. Simplify using `only [coordOf, Sum.elim_inl]`. Rewrite using `[hr, HaarCoord.half_trace_tmul R h2]`. Rewrite using `[psi_gt R σ b _ h, hoff]`.

Conclude with `hS a c`.
-/
theorem psi_coord [CharZero F] {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x)
    (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (b : Module.Basis (Fin d) F E) {S : Matrix (Fin n) (Fin n) (R ⊗[F] E)} (hS : S ∈ HermR R σ n) :
    psi R σ b (coordOf R b S) = S := by
  have hoff : ∀ p : {p : Fin n × Fin n // p.1 < p.2}, offE R b (coordOf R b S) p = S p.1.1 p.1.2 := by
    intro p
    have := (Algebra.TensorProduct.basis R b).sum_repr (S p.1.1 p.1.2)
    conv_rhs => rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [coordOf, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  ext a c
  rcases lt_trichotomy a c with h | h | h
  · rw [psi_lt R σ b _ h, hoff]
  · subst h
    obtain ⟨r, hr⟩ := HaarCoord.fixed_eq_tmul R hinv h2 hδ hσδ (S a a) (hS a a)
    rw [psi_eq]
    simp only [coordOf, Sum.elim_inl]
    rw [hr, HaarCoord.half_trace_tmul R h2]
  · rw [psi_gt R σ b _ h, hoff]
    exact hS a c

/- English proof (translation)
Establish `key : ∀ T : Matrix (Fin n) (Fin n) (R ⊗[F] E), T ∈ HermR R σ n ↔ cT (sigR R σ) T = T`. Introduce `T`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `a c`.

Conclude with `h a c`. Introduce `h a c`. Conclude with `congrFun (congrFun h a) c`. Rewrite `hS`, the goal using `[key]`. Establish `hcc : cT (sigR R σ) (cT (sigR R σ) G) = G`.

Use extensionality with `a c`. Simplify using `[cT, HaarCoord.sigR_sigR R hinv]`. Express the relevant statement in the definitionally equal form `cT (sigR R σ) (cT (sigR R σ) G * S * G) = cT (sigR R σ) G * S * G`. Rewrite using `[cT_mul, cT_mul, hcc, hS, Matrix.mul_assoc]`.
-/
theorem mg_mem {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) (G : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    {S : Matrix (Fin n) (Fin n) (R ⊗[F] E)} (hS : S ∈ HermR R σ n) : mg R σ G S ∈ HermR R σ n := by
  have key : ∀ T : Matrix (Fin n) (Fin n) (R ⊗[F] E), T ∈ HermR R σ n ↔ cT (sigR R σ) T = T := by
    intro T
    constructor
    · intro h
      ext a c
      exact h a c
    · intro h a c
      exact congrFun (congrFun h a) c
  rw [key] at hS ⊢
  have hcc : cT (sigR R σ) (cT (sigR R σ) G) = G := by
    ext a c
    simp [cT, HaarCoord.sigR_sigR R hinv]
  change cT (sigR R σ) (cT (sigR R σ) G * S * G) = cT (sigR R σ) G * S * G
  rw [cT_mul, cT_mul, hcc, hS, Matrix.mul_assoc]

end Alg

section BC

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
variable {d n : ℕ}

def phi : F ⊗[F] E →+* R ⊗[F] E :=
  (Algebra.TensorProduct.map (Algebra.ofId F R) (AlgHom.id F E)).toRingHom

/- English proof (translation)
Simplify using `[phi, Algebra.ofId_apply]`.
-/
theorem phi_tmul (r : F) (e : E) : phi R (r ⊗ₜ[F] e) = algebraMap F R r ⊗ₜ[F] e := by
  simp [phi, Algebra.ofId_apply]

/- English proof (translation)
Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `tmul r e => rw [HaarCoord.sigR_tmul, phi_tmul, phi_tmul, HaarCoord.sigR_tmul]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem phi_sig (σ : E →ₐ[F] E) (y : F ⊗[F] E) : phi R (sigR F σ y) = sigR R σ (phi R y) := by
  induction y with
  | zero => simp
  | tmul r e => rw [HaarCoord.sigR_tmul, phi_tmul, phi_tmul, HaarCoord.sigR_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Establish `h1 : inclR F e = (1 : F) ⊗ₜ[F] e` using `rfl`. Establish `h2 : inclR R e = (1 : R) ⊗ₜ[F] e` using `rfl`. Rewrite using `[h1, h2, phi_tmul, map_one]`.
-/
theorem phi_incl (e : E) : phi R (inclR F e) = inclR R e := by
  have h1 : inclR F e = (1 : F) ⊗ₜ[F] e := rfl
  have h2 : inclR R e = (1 : R) ⊗ₜ[F] e := rfl
  rw [h1, h2, phi_tmul, map_one]

/- English proof (translation)
Simplify using `[offE, map_sum, phi_tmul]`.
-/
theorem offE_map (b : Module.Basis (Fin d) F E) (x : Idx n d → F) (p) :
    phi R (offE F b x p) = offE R b (fun i => algebraMap F R (x i)) p := by
  simp [offE, map_sum, phi_tmul]

/- English proof (translation)
Use extensionality with `a c`. Rewrite using `[Matrix.map_apply]`. Break down `lt_trichotomy a c with h | h | h` into its components or cases. Rewrite using `[psi_lt F σ b _ h, psi_lt R σ b _ h, offE_map]`. Substitute `h` using the available equality.

Rewrite using `[psi_eq, psi_eq, phi_tmul]`. Rewrite using `[psi_gt F σ b _ h, psi_gt R σ b _ h, phi_sig, offE_map]`.
-/
theorem psi_map (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (x : Idx n d → F) :
    (psi F σ b x).map (phi R) = psi R σ b (fun i => algebraMap F R (x i)) := by
  ext a c
  rw [Matrix.map_apply]
  rcases lt_trichotomy a c with h | h | h
  · rw [psi_lt F σ b _ h, psi_lt R σ b _ h, offE_map]
  · subst h
    rw [psi_eq, psi_eq, phi_tmul]
  · rw [psi_gt F σ b _ h, psi_gt R σ b _ h, phi_sig, offE_map]

/- English proof (translation)
Establish `hg : (g.map (inclR F)).map (phi R) = g.map (inclR R)`. Use extensionality with `a c`. Simplify using `[phi_incl]`. Establish `hc : (cT (sigR F σ) (g.map (inclR F))).map (phi R) = cT (sigR R σ) (g.map (inclR R))`. Use extensionality with `a c`.

Simplify using `[cT, phi_sig, phi_incl]`. Express the relevant statement in the definitionally equal form `(cT (sigR F σ) (g.map (inclR F)) * S * g.map (inclR F)).map (phi R) = cT (sigR R σ) (g.map (inclR R)) * S.map (phi R) * g.map (inclR R)`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hg, hc]`.
-/
theorem mg_map (σ : E →ₐ[F] E) (g : Matrix (Fin n) (Fin n) E) (S : Matrix (Fin n) (Fin n) (F ⊗[F] E)) :
    (mg F σ (g.map (inclR F)) S).map (phi R) = mg R σ (g.map (inclR R)) (S.map (phi R)) := by
  have hg : (g.map (inclR F)).map (phi R) = g.map (inclR R) := by
    ext a c
    simp [phi_incl]
  have hc : (cT (sigR F σ) (g.map (inclR F))).map (phi R) = cT (sigR R σ) (g.map (inclR R)) := by
    ext a c
    simp [cT, phi_sig, phi_incl]
  change (cT (sigR F σ) (g.map (inclR F)) * S * g.map (inclR F)).map (phi R) =
    cT (sigR R σ) (g.map (inclR R)) * S.map (phi R) * g.map (inclR R)
  rw [Matrix.map_mul, Matrix.map_mul, hg, hc]

def Lmap (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (g : Matrix (Fin n) (Fin n) E) :
    (Idx n d → R) →ₗ[R] (Idx n d → R) :=
  coordL R b ∘ₗ mg R σ (g.map (inclR R)) ∘ₗ psiL R σ b

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Lmap_apply (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (g : Matrix (Fin n) (Fin n) E)
    (x : Idx n d → R) :
    Lmap R σ b g x = coordOf R b (mg R σ (g.map (inclR R)) (psi R σ b x)) := rfl

/- English proof (translation)
Establish `hH` using `mg_mem F hinv (g.map (inclR F)) (psi_mem F hinv b x)`. Establish `e1` using `psi_coord F hinv h2 hδ hσδ b hH`. Rewrite using `[Lmap_apply, ← psi_map, ← mg_map, ← e1, psi_map, coord_psi R h2]`. Both sides reduce to the same expression.
-/
theorem Lmap_bc [CharZero F] {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x)
    (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (b : Module.Basis (Fin d) F E) (g : Matrix (Fin n) (Fin n) E) (x : Idx n d → F) :
    Lmap R σ b g (fun i => algebraMap F R (x i)) = fun i => algebraMap F R (Lmap F σ b g x i) := by
  have hH := mg_mem F hinv (g.map (inclR F)) (psi_mem F hinv b x)
  have e1 := psi_coord F hinv h2 hδ hσδ b hH
  rw [Lmap_apply, ← psi_map, ← mg_map, ← e1, psi_map, coord_psi R h2]
  rfl

def Amat (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (g : Matrix (Fin n) (Fin n) E) :
    Matrix (Idx n d) (Idx n d) F :=
  LinearMap.toMatrix' (Lmap F σ b g)

/- English proof (translation)
Establish `key : (Amat σ b g).map (algebraMap F R) = LinearMap.toMatrix' (Lmap R σ b g)`. Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Amat, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply]`. Establish `e : (Pi.single j (1 : R) : Idx n d → R) = fun j' => algebraMap F R ((Pi.single j (1 : F) : Idx n d → F) j')`. Use function extensionality and compare the values at `j'`.

Simplify using `only [Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e, Lmap_bc R hinv h2 hδ hσδ]`. Rewrite using `[key, LinearMap.toMatrix'_mulVec]`.
-/
theorem Amat_spec [CharZero F] {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x)
    (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (b : Module.Basis (Fin d) F E) (g : Matrix (Fin n) (Fin n) E) (x : Idx n d → R) :
    (Amat σ b g).map (algebraMap F R) *ᵥ x = Lmap R σ b g x := by
  have key : (Amat σ b g).map (algebraMap F R) = LinearMap.toMatrix' (Lmap R σ b g) := by
    ext i j
    rw [Matrix.map_apply, Amat, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply]
    have e : (Pi.single j (1 : R) : Idx n d → R) =
        fun j' => algebraMap F R ((Pi.single j (1 : F) : Idx n d → F) j') := by
      funext j'
      simp only [Pi.single_apply]
      split_ifs <;> simp
    rw [e, Lmap_bc R hinv h2 hδ hσδ]
  rw [key, LinearMap.toMatrix'_mulVec]

/- English proof (translation)
Establish `hH` using `mg_mem (F := F) R hinv (g'.map (inclR R)) (psi_mem R hinv b x)`. Establish `e1` using `psi_coord R hinv h2 hδ hσδ b hH`. Establish `hone : g'.map (inclR (F` using `F) R) * g.map (inclR (F := F) R) = 1 := by`. Rewrite using `[← Matrix.map_mul, hgg, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[Lmap_apply R σ b g, Lmap_apply R σ b g', e1]`.

Establish `: mg R σ (g.map (inclR R)) (mg R σ (g'.map (inclR R)) (psi R σ b x)) = psi R σ b x`. Express the relevant statement in the definitionally equal form `cT (sigR R σ) (g.map (inclR R)) * (cT (sigR R σ) (g'.map (inclR R)) * psi R σ b x * g'.map (inclR R)) * g.map (inclR R) = _`. Establish `: cT (sigR R σ) (g.map (inclR R)) * cT (sigR R σ) (g'.map (inclR R)) = 1`. Rewrite using `[← cT_mul, hone, cT_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[this, coord_psi R h2]`.
-/
theorem Lmap_inv [CharZero F] {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x)
    (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (b : Module.Basis (Fin d) F E) {g g' : Matrix (Fin n) (Fin n) E} (hgg : g' * g = 1)
    (x : Idx n d → R) : Lmap R σ b g (Lmap R σ b g' x) = x := by
  have hH := mg_mem (F := F) R hinv (g'.map (inclR R)) (psi_mem R hinv b x)
  have e1 := psi_coord R hinv h2 hδ hσδ b hH
  have hone : g'.map (inclR (F := F) R) * g.map (inclR (F := F) R) = 1 := by
    rw [← Matrix.map_mul, hgg, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Lmap_apply R σ b g, Lmap_apply R σ b g', e1]
  have : mg R σ (g.map (inclR R)) (mg R σ (g'.map (inclR R)) (psi R σ b x)) = psi R σ b x := by
    change cT (sigR R σ) (g.map (inclR R)) *
        (cT (sigR R σ) (g'.map (inclR R)) * psi R σ b x * g'.map (inclR R)) * g.map (inclR R) = _
    have : cT (sigR R σ) (g.map (inclR R)) * cT (sigR R σ) (g'.map (inclR R)) = 1 := by
      rw [← cT_mul, hone, cT_one]
    calc _ = (cT (sigR R σ) (g.map (inclR R)) * cT (sigR R σ) (g'.map (inclR R))) * psi R σ b x *
          (g'.map (inclR R) * g.map (inclR R)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [this, hone, Matrix.one_mul, Matrix.mul_one]
  rw [this, coord_psi R h2]

/- English proof (translation)
Establish `hgg : g⁻¹ * g = 1` using `Matrix.nonsing_inv_mul g (isUnit_iff_ne_zero.mpr hg)`. Establish `: Amat σ b g * Amat σ b g⁻¹ = 1`. Rewrite using `[Amat, Amat, ← LinearMap.toMatrix'_comp]`. Establish `: Lmap F σ b g ∘ₗ Lmap F σ b g⁻¹ = LinearMap.id` using `LinearMap.ext fun x => Lmap_inv F hinv h2 hδ hσδ b hgg x`. Rewrite using `[this, LinearMap.toMatrix'_id]`.

Conclude with `(Matrix.isUnit_det_of_right_inverse this).ne_zero`.
-/
theorem Amat_det [CharZero F] {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x)
    (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (b : Module.Basis (Fin d) F E) {g : Matrix (Fin n) (Fin n) E} (hg : g.det ≠ 0) :
    (Amat σ b g).det ≠ 0 := by
  have hgg : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g (isUnit_iff_ne_zero.mpr hg)
  have : Amat σ b g * Amat σ b g⁻¹ = 1 := by
    rw [Amat, Amat, ← LinearMap.toMatrix'_comp]
    have : Lmap F σ b g ∘ₗ Lmap F σ b g⁻¹ = LinearMap.id :=
       LinearMap.ext fun x => Lmap_inv F hinv h2 hδ hσδ b hgg x
    rw [this, LinearMap.toMatrix'_id]
  exact (Matrix.isUnit_det_of_right_inverse this).ne_zero

end BC

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
variable {d n : ℕ}

/- English proof (translation)
Use `IsModuleTopology.continuous_of_linearMap (R := R) (A := R) (B := R ⊗[F] E) (LinearMap.toSpanSingleton R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e))` as an intermediate fact. Establish `h : (fun r : R => r ⊗ₜ[F] e) = ⇑(LinearMap.toSpanSingleton R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e))`. Use function extensionality and compare the values at `r`. Simplify using `[TensorProduct.smul_tmul']`. Rewrite using `[h]`.

Conclude with `this`.
-/
theorem continuous_tmul [IsTopologicalRing R] [ContinuousAdd (R ⊗[F] E)]
    [ContinuousSMul R (R ⊗[F] E)] (e : E) : Continuous fun r : R => r ⊗ₜ[F] e := by
  have := IsModuleTopology.continuous_of_linearMap (R := R) (A := R) (B := R ⊗[F] E)
    (LinearMap.toSpanSingleton R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e))
  have h : (fun r : R => r ⊗ₜ[F] e) =
      ⇑(LinearMap.toSpanSingleton R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e)) := by
    funext r
    simp [TensorProduct.smul_tmul']
  rw [h]
  exact this

/- English proof (translation)
The claim follows from `continuous_finset_sum _ fun k _ => (continuous_tmul R (b k)).comp (continuous_apply _)`.
-/
theorem continuous_offE [IsTopologicalRing R] [ContinuousAdd (R ⊗[F] E)]
    [ContinuousSMul R (R ⊗[F] E)] (b : Module.Basis (Fin d) F E) (p) :
    Continuous fun x : Idx n d → R => offE R b x p :=
  continuous_finset_sum _ fun k _ => (continuous_tmul R (b k)).comp (continuous_apply _)

/- English proof (translation)
Use `continuous_matrix fun a c => ?_` and prove the remaining obligations. Break down `lt_trichotomy a c with h | h | h` into its components or cases. Simplify using `only [psi_lt R σ b _ h]`. Conclude with `continuous_offE R b _`. Substitute `h` using the available equality.

Simplify using `only [psi_eq]`. Conclude with `(continuous_tmul R (1 : E)).comp (continuous_apply _)`. Simplify using `only [psi_gt R σ b _ h]`. Conclude with `hsig.comp (continuous_offE R b _)`.
-/
theorem continuous_psi [IsTopologicalRing R] [ContinuousAdd (R ⊗[F] E)]
    [ContinuousSMul R (R ⊗[F] E)] {σ : E →ₐ[F] E} (hsig : Continuous (sigR R σ))
    (b : Module.Basis (Fin d) F E) :
    Continuous (psi R σ b : (Idx n d → R) → Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  refine continuous_matrix fun a c => ?_
  rcases lt_trichotomy a c with h | h | h
  · simp only [psi_lt R σ b _ h]
    exact continuous_offE R b _
  · subst h
    simp only [psi_eq]
    exact (continuous_tmul R (1 : E)).comp (continuous_apply _)
  · simp only [psi_gt R σ b _ h]
    exact hsig.comp (continuous_offE R b _)

/- English proof (translation)
Use `continuous_pi fun i => ?_` and prove the remaining obligations. Break down `i with i | q` into its components or cases. Conclude with `continuous_const.mul (htr.comp (continuous_apply_apply i i))`. Conclude with `((continuous_apply q.2).comp hrepr.continuous).comp (continuous_apply_apply q.1.1.1 q.1.1.2)`.
-/
theorem continuous_coordOf [IsTopologicalRing R] (b : Module.Basis (Fin d) F E)
    (htr : Continuous (Algebra.trace R (R ⊗[F] E)))
    (hrepr : IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k) :
    Continuous (coordOf R b : Matrix (Fin n) (Fin n) (R ⊗[F] E) → Idx n d → R) := by
  refine continuous_pi fun i => ?_
  rcases i with i | q
  · exact continuous_const.mul (htr.comp (continuous_apply_apply i i))
  · exact ((continuous_apply q.2).comp hrepr.continuous).comp
      (continuous_apply_apply q.1.1.1 q.1.1.2)

end Top

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R`. Establish `h2 : Module.finrank F E = 2` using `hcm.2.2.1`. Take `⟨hinv, δ, hδ, hσδ⟩` from `HaarCoord.conj_facts hcm`. Use `haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`.

Use `haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _`. Use `haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩`. Set `K : (Idx n d → R) ≃ₜ HermR R σ n` to `{ toFun := fun x => ⟨psi R σ b x, psi_mem R hinv b x⟩ invFun := fun S => coordOf R b (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) left_inv := fun x => coord_psi R h2 σ b x right_inv := fun S => Subtype.ext (psi_coord R hinv h2 hδ hσδ b S.2) continuous_toFun := (continuous_psi R t5 b). …`. Establish `hKadd : ∀ x y, K (x + y) = K x + K y` using `fun x y => Subtype.ext ((psiL R σ b).map_add x y)`. Set `e : (Idx n d → R) ≃+ HermR R σ n` to `AddEquiv.mk' K.toEquiv hKadd`.

Establish `hμ : (ν.map K.symm).IsAddHaarMeasure` using `e.symm.isAddHaarMeasure_map ν K.symm.continuous K.continuous`. Set `T : (Idx n d → R) → (Idx n d → R)` to `fun x => (Amat σ b g).map (algebraMap F R) *ᵥ x`. Establish `hT : Continuous T` using `continuous_const.matrix_mulVec continuous_id`. Establish `hτeq : τ = K ∘ T ∘ K.symm`. Use function extensionality and compare the values at `S`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `hS : psi R σ b (coordOf R b (S : Matrix (Fin n) (Fin n) (R ⊗[F] E))) = S` using `psi_coord R hinv h2 hδ hσδ b S.2`. Establish `hM : (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = mg R σ (g.map (inclR R)) (S : Matrix (Fin n) (Fin n) (R ⊗[F] E))` using `hτ S`. Express the relevant statement in the definitionally equal form `(τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = psi R σ b (T (coordOf R b S.1))`. Simplify using `only [T]`.

Rewrite using `[Amat_spec R hinv h2 hδ hσδ, Lmap_apply, hS, ← hM]`. Conclude with `(psi_coord R hinv h2 hδ hσδ b (τ S).2).symm`. Rewrite using `[hτeq, ← Measure.map_map K.continuous.measurable (hT.measurable.comp K.symm.continuous.measurable), ← Measure.map_map hT.measurable K.symm.continuous.measurable, hc _ hμ, Measure.map_smul, Measure.map_map K.continuous.measurable K.symm.continuous.measurable]`. Simplify using the standard rewrite rules.
-/
theorem map_eq_of_coord {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
    {d n : ℕ} (b : Module.Basis (Fin d) F E) (g : Matrix (Fin n) (Fin n) E) (c : ℝ≥0)
    (hc : ∀ μ : Measure (Idx n d → R), μ.IsAddHaarMeasure →
      μ.map (fun x => (Amat σ b g).map (algebraMap F R) *ᵥ x) = c • μ)
    (ν : Measure (HermR R σ n)) (hν : ν.IsAddHaarMeasure) (τ : HermR R σ n → HermR R σ n)
    (hτ : ∀ S, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      cT (sigR R σ) (g.map (inclR R)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g.map (inclR R)) :
    ν.map τ = c • ν := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hcm
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩
  let K : (Idx n d → R) ≃ₜ HermR R σ n :=
    { toFun := fun x => ⟨psi R σ b x, psi_mem R hinv b x⟩
      invFun := fun S => coordOf R b (S : Matrix (Fin n) (Fin n) (R ⊗[F] E))
      left_inv := fun x => coord_psi R h2 σ b x
      right_inv := fun S => Subtype.ext (psi_coord R hinv h2 hδ hσδ b S.2)
      continuous_toFun := (continuous_psi R t5 b).subtype_mk _
      continuous_invFun := (continuous_coordOf R b t6 (t7 d b)).comp continuous_subtype_val }
  have hKadd : ∀ x y, K (x + y) = K x + K y := fun x y =>
    Subtype.ext ((psiL R σ b).map_add x y)
  let e : (Idx n d → R) ≃+ HermR R σ n := AddEquiv.mk' K.toEquiv hKadd
  have hμ : (ν.map K.symm).IsAddHaarMeasure :=
    e.symm.isAddHaarMeasure_map ν K.symm.continuous K.continuous
  let T : (Idx n d → R) → (Idx n d → R) := fun x => (Amat σ b g).map (algebraMap F R) *ᵥ x
  have hT : Continuous T := continuous_const.matrix_mulVec continuous_id
  have hτeq : τ = K ∘ T ∘ K.symm := by
    funext S
    apply Subtype.ext
    have hS : psi R σ b (coordOf R b (S : Matrix (Fin n) (Fin n) (R ⊗[F] E))) = S :=
      psi_coord R hinv h2 hδ hσδ b S.2
    have hM : (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
        mg R σ (g.map (inclR R)) (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := hτ S
    change (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = psi R σ b (T (coordOf R b S.1))
    simp only [T]
    rw [Amat_spec R hinv h2 hδ hσδ, Lmap_apply, hS, ← hM]
    exact (psi_coord R hinv h2 hδ hσδ b (τ S).2).symm
  rw [hτeq, ← Measure.map_map K.continuous.measurable (hT.measurable.comp K.symm.continuous.measurable),
    ← Measure.map_map hT.measurable K.symm.continuous.measurable, hc _ hμ, Measure.map_smul,
    Measure.map_map K.continuous.measurable K.symm.continuous.measurable]
  simp

end Main

end GlobalTheory.CompanionTheory.SW.PfHerm

namespace GlobalTheory.CompanionTheory.SW

open PfHerm

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm n g hg`. Establish `h2 : Module.finrank F E = 2` using `hcm.2.2.1`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)`. Take `⟨hinv, δ, hδ, hσδ⟩` from `HaarCoord.conj_facts hcm`. Set `b : Module.Basis (Fin 2) F E` to `Module.finBasisOfFinrankEq F E h2`.

Take `⟨cinf, c, hU, hI, hF⟩` from `GlobalTheory.T.addHaar_map_mulVec_eq_smul_at_all_places F (Idx n 2) (Amat σ b g) (Amat_det hinv h2 hδ hσδ b hg)`. Use `⟨cinf, c, hU, ?_, fun v => ?_⟩` and prove the remaining obligations. Take `⟨l1, l2, l3, l4, -⟩` from `isLocR_Ainf F hcm.1 haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Conclude with `fun ν hν τ hτ => map_eq_of_coord hcm (Ainf F) b g cinf hI ν hν τ hτ`. Take `⟨l1, l2, l3, l4, -⟩` from `LocFv.isLocR_Fv F v haveI : BorelSpace (Fv F v) := ⟨rfl⟩`.

Conclude with `fun ν hν τ hτ => map_eq_of_coord hcm (Fv F v) b g (c v) (hF v) ν hν τ hτ`.
-/
theorem pf_herm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) E), g.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure → ∀ τ : HermR (Ainf F) σ n → HermR (Ainf F) σ n, (∀ S, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = cT (sigR (Ainf F) σ) (g.map (inclR (Ainf F))) * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g.map (inclR (Ainf F))) → ν.map τ = cinf • ν) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ ν : Measure (HermR (Fv F v) σ n), ν.IsAddHaarMeasure → ∀ τ : HermR (Fv F v) σ n → HermR (Fv F v) σ n, (∀ S, (τ S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) (g.map (inclR (Fv F v))) * (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * g.map (inclR (Fv F v))) → ν.map τ = c v • ν) := by
  intro F E _ _ _ _ _ σ hcm n g hg
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hcm
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
  obtain ⟨cinf, c, hU, hI, hF⟩ := GlobalTheory.T.addHaar_map_mulVec_eq_smul_at_all_places F (Idx n 2) (Amat σ b g)
    (Amat_det hinv h2 hδ hσδ b hg)
  refine ⟨cinf, c, hU, ?_, fun v => ?_⟩
  · obtain ⟨l1, l2, l3, l4, -⟩ := isLocR_Ainf F hcm.1
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    exact fun ν hν τ hτ => map_eq_of_coord hcm (Ainf F) b g cinf hI ν hν τ hτ
  · obtain ⟨l1, l2, l3, l4, -⟩ := LocFv.isLocR_Fv F v
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact fun ν hν τ hτ => map_eq_of_coord hcm (Fv F v) b g (c v) (hF v) ν hν τ hτ

end GlobalTheory.CompanionTheory.SW
