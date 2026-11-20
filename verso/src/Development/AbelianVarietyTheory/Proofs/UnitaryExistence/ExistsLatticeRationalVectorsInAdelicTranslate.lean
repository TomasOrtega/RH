import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat.Translate

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Use extensionality with `i`. Simplify using `[fv, TensorProduct.tmul_add]`.
-/
lemma fv_add (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  ext i; simp [fv, TensorProduct.tmul_add]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[fv]`.
-/
lemma fv_zero : fv F (0 : Fin n → E) = 0 := by
  ext i; simp [fv]

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero => simp [fv_zero]`. Consider the case `succ k ih => rw [succ_nsmul, succ_nsmul, fv_add, ih]`.
-/
lemma fv_nsmul (d : ℕ) (x : Fin n → E) : fv F (d • x) = d • fv F x := by
  induction d with
  | zero => simp [fv_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, fv_add, ih]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[fv]`.
-/
lemma fv_smul (b : E) (x : Fin n → E) :
    fv F (b • x) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b : RA F E) • fv F x := by
  ext i; simp [fv]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[fv]`.
-/
lemma gen_eq (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => (a ⊗ₜ[F] x i : RA F E)) = (a ⊗ₜ[F] (1 : E) : RA F E) • fv F x := by
  ext i; simp [fv]

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩`.
-/
lemma fv_mem_hat {S : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ S) : fv F x ∈ hat F S :=
  AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a', ha', x, hx, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨a * a', fun v => mul_mem (ha v) (ha' v), x, hx, ?_⟩` and prove the remaining obligations. Use extensionality with `i`.

Simplify using the standard rewrite rules. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`.

Conclude with `neg_mem hx`.
-/
lemma hat_smul_int {S : Set (Fin n → E)} {a : FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {z : Fin n → RA F E} (hz : z ∈ hat F S) :
    (a ⊗ₜ[F] (1 : E) : RA F E) • z ∈ hat F S := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * a', fun v => mul_mem (ha v) (ha' v), x, hx, ?_⟩
    ext i; simp
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a', ha', x, hx, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨a', ha', b • x, L.smul_mem b hx, ?_⟩` and prove the remaining obligations. Use extensionality with `i`.

Simplify using `[Algebra.smul_def]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`.

Conclude with `neg_mem hx`.
-/
lemma hat_smul_ring (L : Submodule (𝓞 E) (Fin n → E)) (b : 𝓞 E) {z : Fin n → RA F E}
    (hz : z ∈ hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) : RA F E) • z ∈ hat F (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a', ha', b • x, L.smul_mem b hx, ?_⟩
    ext i; simp [Algebra.smul_def]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

def pre (M : Matrix (Fin n) (Fin n) (RA F E)) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) where
  carrier := {v | M.mulVec (fv F v) ∈ hat F (L : Set (Fin n → E))}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at *
    rw [fv_add, Matrix.mulVec_add]; exact add_mem hx hy
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [fv_zero, Matrix.mulVec_zero]; exact zero_mem _
  smul_mem' := by
    intro b x hx
    simp only [Set.mem_ofPred_eq] at *
    have : b • x = (b : E) • x := rfl
    rw [this, fv_smul, Matrix.mulVec_smul]
    exact hat_smul_ring L b hx

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
lemma mem_pre {M : Matrix (Fin n) (Fin n) (RA F E)} {L : Submodule (𝓞 E) (Fin n → E)} {v : Fin n → E} :
    v ∈ pre M L ↔ M.mulVec (fv F v) ∈ hat F (L : Set (Fin n → E)) := Iff.rfl

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a', ha', x, hx, rfl⟩` from `hz`. Rewrite using `[gen_eq, Matrix.mulVec_smul]`. Conclude with `hat_smul_int ha' (hS hx)`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [Matrix.mulVec_neg]`. Conclude with `neg_mem hx`.
-/
lemma mulVec_mem_hat {M : Matrix (Fin n) (Fin n) (RA F E)} {L : Submodule (𝓞 E) (Fin n → E)}
    {S : Set (Fin n → E)} (hS : S ⊆ pre M L) {z : Fin n → RA F E} (hz : z ∈ hat F S) :
    M.mulVec z ∈ hat F (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    rw [gen_eq, Matrix.mulVec_smul]
    exact hat_smul_int ha' (hS hx)
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

/- English proof (translation)
Use `choose f hf0 hf using h`. Take `⟨s, hs⟩` from `hL`. Use `⟨∏ x ∈ s, f (M.mulVec (fv F x)), Finset.prod_pos fun _ _ => hf0 _, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.smul_mulVec]`. Use `mulVec_mem_hat ?_ hz` and prove the remaining obligations.

Establish `: L ≤ pre ((∏ x ∈ s, f (M.mulVec (fv F x))) • M) L` using `by conv_lhs => rw [← hs]`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem (fun x => f (M.mulVec (fv F x))) (Finset.mem_coe.1 hx)`. Rewrite using `[SetLike.mem_coe, mem_pre, Matrix.smul_mulVec, hk, mul_comm, mul_smul]`.

Conclude with `nsmul_mem (hf _) _`. Conclude with `this`.
-/
lemma exists_bound (M : Matrix (Fin n) (Fin n) (RA F E)) {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
    (h : ∀ z : Fin n → RA F E, ∃ d : ℕ, 0 < d ∧ d • z ∈ hat F (L : Set (Fin n → E))) :
    ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), d • M.mulVec z ∈ hat F (L : Set (Fin n → E)) := by
  classical
  choose f hf0 hf using h
  obtain ⟨s, hs⟩ := hL
  refine ⟨∏ x ∈ s, f (M.mulVec (fv F x)), Finset.prod_pos fun _ _ => hf0 _, fun z hz => ?_⟩
  rw [← Matrix.smul_mulVec]
  refine mulVec_mem_hat ?_ hz
  have : L ≤ pre ((∏ x ∈ s, f (M.mulVec (fv F x))) • M) L := by
    conv_lhs => rw [← hs]
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => f (M.mulVec (fv F x))) (Finset.mem_coe.1 hx)
    rw [SetLike.mem_coe, mem_pre, Matrix.smul_mulVec, hk, mul_comm, mul_smul]
    exact nsmul_mem (hf _) _
  exact this

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a', ha', x, hx, rfl⟩` from `hz`. Rewrite using `[gen_eq, smul_comm, ← fv_nsmul]`. Conclude with `hat_smul_int ha' (fv_mem_hat (h x hx))`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
lemma nsmul_mem_hat {S S' : Set (Fin n → E)} {d : ℕ} (h : ∀ x ∈ S, d • x ∈ S') {z : Fin n → RA F E}
    (hz : z ∈ hat F S) : d • z ∈ hat F S' := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    rw [gen_eq, smul_comm, ← fv_nsmul]
    exact hat_smul_int ha' (fv_mem_hat (h x hx))
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Rewrite `h` using `[← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F]`. Establish `hd' : (d : F) ≠ 0` using `by exact_mod_cast hd.ne'`. Use `congrArg (fun z => (d : F)⁻¹ • z) h` as an intermediate fact. Simplify `this` using `[smul_smul, inv_mul_cancel₀ hd']`.
-/
lemma nsmul_cancel {d : ℕ} (hd : 0 < d) {x y : Fin n → RA F E} (h : d • x = d • y) : x = y := by
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd.ne'
  have := congrArg (fun z => (d : F)⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ hd'] using this

end GlobalTheory.AdLat.Translate

open GlobalTheory.AdLat.Translate in

/- English proof (translation)
Introduce `F E _ _ _ _ _ n L g hL hspan`. Take `⟨h1, h2, -, h4⟩` from `GlobalTheory.AdLat.hat_rational_points_and_approx F E n L hL hspan`. Use `set G : Matrix (Fin n) (Fin n) (RA F E) := (g : Matrix (Fin n) (Fin n) (RA F E)) with hG`. Use `set H : Matrix (Fin n) (Fin n) (RA F E) := ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) with hH`. Establish `hGH : ∀ z, G.mulVec (H.mulVec z) = z`.

Introduce `z`. Rewrite using `[Matrix.mulVec_mulVec, hG, hH, Units.mul_inv, Matrix.one_mulVec]`. Establish `hHG : ∀ z, H.mulVec (G.mulVec z) = z`. Introduce `z`. Rewrite using `[Matrix.mulVec_mulVec, hG, hH, Units.inv_mul, Matrix.one_mulVec]`.

Establish `him : ∀ z, z ∈ G.mulVec '' (hat F (L : Set (Fin n → E)) : Set (Fin n → RA F E)) ↔ H.mulVec z ∈ hat F (L : Set (Fin n → E))`. Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Rewrite using `[hHG]`.

Conclude with `hu`. Introduce `h`. Conclude with `⟨_, h, hGH z⟩`. Take `⟨d, hd, hdG⟩` from `exists_bound G hL h4`. Take `⟨e, he, heH⟩` from `exists_bound H hL h4`.

Establish `hd' : (d : E) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `he' : (e : E) ≠ 0` using `by exact_mod_cast he.ne'`. Establish `hlow : ∀ x ∈ L, e • x ∈ pre H L`. Introduce `x hx`. Rewrite using `[mem_pre, fv_nsmul, Matrix.mulVec_smul]`.

Conclude with `heH _ (fv_mem_hat hx)`. Establish `hup : ∀ x ∈ pre H L, d • x ∈ L`. Introduce `x hx`. Rewrite using `[← h1, fv_nsmul, ← hGH (fv F x)]`. Conclude with `hdG _ hx`.

Use `⟨pre H L, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Conclude with `(him _).symm`. Establish `hinj : Function.Injective (d • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E)))`. Introduce `x y hxy`.

Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply] at hxy`. Rewrite `hxy` using `[← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E]`. Conclude with `smul_right_injective _ hd' hxy`. Use `Submodule.fg_of_fg_map_injective _ hinj ?_` and prove the remaining obligations. Establish `hle : (pre H L).map (d • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) ≤ L`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hup x hx`. Establish `: IsNoetherian (𝓞 E) L` using `isNoetherian_of_fg_of_noetherian _ hL`. Conclude with `(isNoetherian_submodule.1 this) _ hle`. Rewrite using `[eq_top_iff, ← hspan, Submodule.span_le]`.

Introduce `x hx`. Establish `hx' : x = (e : E)⁻¹ • (e • x)`. Rewrite using `[← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ he', one_smul]`. Rewrite using `[hx']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (hlow x hx))`.

Use extensionality with `z`. Rewrite using `[him]`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Conclude with `mulVec_mem_hat subset_rfl hz`.

Introduce `hz`. Establish `hdz : d • z ∈ hat F (L : Set (Fin n → E))`. Rewrite using `[← hGH z]`. Conclude with `hdG _ hz`. Take `⟨x, -, w, hw, hxw⟩` from `h2 (d * e) (Nat.mul_pos hd he) _ hdz`.

Establish `hx' : x = d • ((d : E)⁻¹ • x)`. Rewrite using `[← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hd', one_smul]`. Establish `hz' : z = fv F ((d : E)⁻¹ • x) + e • w`. Apply `nsmul_cancel hd` to reduce the goal to its premises. Rewrite using `[smul_add, ← fv_nsmul, ← hx', smul_smul, hxw]`.

Establish `hy : (d : E)⁻¹ • x ∈ pre H L`. Rewrite using `[mem_pre, eq_sub_of_add_eq hz'.symm, Matrix.mulVec_sub, Matrix.mulVec_smul]`. Conclude with `sub_mem hz (heH _ hw)`. Rewrite using `[hz']`. Conclude with `add_mem (fv_mem_hat hy) (nsmul_mem_hat hlow hw)`.
-/
theorem GlobalTheory.AdLat.exists_lattice_latOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∃ Λ : Submodule (𝓞 E) (Fin n → E), (Λ : Set (Fin n → E)) = latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L ∧ Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧ (hat F (Λ : Set (Fin n → E)) : Set (Fin n → RA F E)) = (g : Matrix (Fin n) (Fin n) (RA F E)).mulVec '' (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L g hL hspan
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.AdLat.hat_rational_points_and_approx F E n L hL hspan
  set G : Matrix (Fin n) (Fin n) (RA F E) := (g : Matrix (Fin n) (Fin n) (RA F E)) with hG
  set H : Matrix (Fin n) (Fin n) (RA F E) := ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E))
    with hH
  have hGH : ∀ z, G.mulVec (H.mulVec z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, hG, hH, Units.mul_inv, Matrix.one_mulVec]
  have hHG : ∀ z, H.mulVec (G.mulVec z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, hG, hH, Units.inv_mul, Matrix.one_mulVec]
  have him : ∀ z, z ∈ G.mulVec '' (hat F (L : Set (Fin n → E)) : Set (Fin n → RA F E)) ↔
      H.mulVec z ∈ hat F (L : Set (Fin n → E)) := by
    intro z
    constructor
    · rintro ⟨u, hu, rfl⟩; rw [hHG]; exact hu
    · intro h; exact ⟨_, h, hGH z⟩
  obtain ⟨d, hd, hdG⟩ := exists_bound G hL h4
  obtain ⟨e, he, heH⟩ := exists_bound H hL h4
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  have he' : (e : E) ≠ 0 := by exact_mod_cast he.ne'
  have hlow : ∀ x ∈ L, e • x ∈ pre H L := by
    intro x hx
    rw [mem_pre, fv_nsmul, Matrix.mulVec_smul]
    exact heH _ (fv_mem_hat hx)
  have hup : ∀ x ∈ pre H L, d • x ∈ L := by
    intro x hx
    rw [← h1, fv_nsmul, ← hGH (fv F x)]
    exact hdG _ hx
  refine ⟨pre H L, ?_, ?_, ?_, ?_⟩
  · ext v
    exact (him _).symm
  · have hinj : Function.Injective (d • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) := by
      intro x y hxy
      simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
      rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E] at hxy
      exact smul_right_injective _ hd' hxy
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have hle : (pre H L).map (d • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) ≤ L := by
      rintro _ ⟨x, hx, rfl⟩
      exact hup x hx
    have : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian _ hL
    exact (isNoetherian_submodule.1 this) _ hle
  · rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro x hx
    have hx' : x = (e : E)⁻¹ • (e • x) := by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ he', one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hlow x hx))
  · ext z
    rw [him]
    constructor
    · intro hz
      exact mulVec_mem_hat subset_rfl hz
    · intro hz
      have hdz : d • z ∈ hat F (L : Set (Fin n → E)) := by
        rw [← hGH z]; exact hdG _ hz
      obtain ⟨x, -, w, hw, hxw⟩ := h2 (d * e) (Nat.mul_pos hd he) _ hdz
      have hx' : x = d • ((d : E)⁻¹ • x) := by
        rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hd', one_smul]
      have hz' : z = fv F ((d : E)⁻¹ • x) + e • w := by
        apply nsmul_cancel hd
        rw [smul_add, ← fv_nsmul, ← hx', smul_smul, hxw]
      have hy : (d : E)⁻¹ • x ∈ pre H L := by
        rw [mem_pre, eq_sub_of_add_eq hz'.symm, Matrix.mulVec_sub, Matrix.mulVec_smul]
        exact sub_mem hz (heH _ hw)
      rw [hz']
      exact add_mem (fv_mem_hat hy) (nsmul_mem_hat hlow hw)
