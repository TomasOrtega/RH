import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximationStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslateStatement

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat.Tower

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[fv, TensorProduct.tmul_add]`.
-/
lemma fv_add (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  funext i; simp [fv, TensorProduct.tmul_add]

omit [NumberField E] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[fv, TensorProduct.tmul_sub]`.
-/
lemma fv_sub (x y : Fin n → E) : fv F (x - y) = fv F x - fv F y := by
  funext i; simp [fv, TensorProduct.tmul_sub]

omit [NumberField E] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[fv]`.
-/
lemma fv_zero : fv F (0 : Fin n → E) = 0 := by
  funext i; simp [fv]

omit [NumberField E] in
/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp [fv_zero]`. Consider the case `succ k ih => rw [succ_nsmul, succ_nsmul, fv_add, ih]`.
-/
lemma fv_nsmul (N : ℕ) (x : Fin n → E) : fv F (N • x) = N • fv F x := by
  induction N with
  | zero => simp [fv_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, fv_add, ih]

omit [NumberField E] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [fv, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Both sides reduce to the same expression.
-/
lemma fv_smul (c : 𝓞 E) (x : Fin n → E) :
    fv F (c • x) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E) : RA F E) • fv F x := by
  funext i
  simp only [fv, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

omit [NumberField E] in
/- English proof (translation)
Establish `hN' : (N : F) ≠ 0` using `by exact_mod_cast hN.ne'`. Rewrite `h` using `[← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F]`. Use `congrArg (fun t => (N : F)⁻¹ • t) h` as an intermediate fact. Simplify `this` using `[smul_smul, inv_mul_cancel₀ hN']`.
-/
lemma nsmul_cancel {N : ℕ} (hN : 0 < N) {z u : Fin n → RA F E} (h : N • z = N • u) : z = u := by
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  have := congrArg (fun t => (N : F)⁻¹ • t) h
  simpa [smul_smul, inv_mul_cancel₀ hN'] using this

omit [NumberField E] in
/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨a, ha, c • x, L.smul_mem c hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Both sides reduce to the same expression. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`.

Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
lemma smul_mem_hat (L : Submodule (𝓞 E) (Fin n → E)) (c : 𝓞 E) {z : Fin n → RA F E}
    (hz : z ∈ hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E) : RA F E) • z ∈ hat F (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, c • x, L.smul_mem c hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Establish `hN' : (N : E) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `h1 : N • ((N : E)⁻¹ • (x : Fin n → E)) = x`. Rewrite using `[← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hN', one_smul]`. Establish `h2 : fv F ((N : E)⁻¹ • (x : Fin n → E)) = u`. Apply `nsmul_cancel hN` to reduce the goal to its premises.

Rewrite using `[← fv_nsmul, h1, h]`. Use `⟨⟨_, (hM _).1 (h2 ▸ hu)⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Conclude with `h1.symm`.
-/
lemma exists_div {M : Submodule (𝓞 E) (Fin n → E)}
    (hM : ∀ v, fv F v ∈ hat F (M : Set (Fin n → E)) ↔ v ∈ M) {N : ℕ} (hN : 0 < N)
    (x : M) {u : Fin n → RA F E} (hu : u ∈ hat F (M : Set (Fin n → E)))
    (h : fv F (x : Fin n → E) = N • u) : ∃ v : M, x = N • v := by
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : N • ((N : E)⁻¹ • (x : Fin n → E)) = x := by
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hN', one_smul]
  have h2 : fv F ((N : E)⁻¹ • (x : Fin n → E)) = u := by
    apply nsmul_cancel hN
    rw [← fv_nsmul, h1, h]
  refine ⟨⟨_, (hM _).1 (h2 ▸ hu)⟩, Subtype.ext ?_⟩
  exact h1.symm

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL`. Use `haveI : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _`. Use `haveI : Module.Flat (𝓞 E) L := inferInstance`. Conclude with `Module.Flat.projective_of_finitePresentation`.
-/
lemma projective_of_fg (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    Module.Projective (𝓞 E) L := by
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  haveI : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  haveI : Module.Flat (𝓞 E) L := inferInstance
  exact Module.Flat.projective_of_finitePresentation

omit [NumberField E] in
/- English proof (translation)
The claim follows from `map_nsmul g.mulVecLin N z`.
-/
lemma mulVec_nsmul (g : Matrix (Fin n) (Fin n) (RA F E)) (N : ℕ) (z : Fin n → RA F E) :
    g *ᵥ (N • z) = N • (g *ᵥ z) := map_nsmul g.mulVecLin N z

def rel (L Λ : Submodule (𝓞 E) (Fin n → E)) (g : Matrix (Fin n) (Fin n) (RA F E)) (N : ℕ) :
    Submodule (𝓞 E) (L × Λ) where
  carrier := {p | ∃ w ∈ hat F (L : Set (Fin n → E)),
    fv F (p.2 : Fin n → E) = g *ᵥ (fv F (p.1 : Fin n → E) + N • w)}
  zero_mem' := ⟨0, zero_mem _, by simp [fv_zero]⟩
  add_mem' := by
    rintro p q ⟨w, hw, hp⟩ ⟨w', hw', hq⟩
    refine ⟨w + w', add_mem hw hw', ?_⟩
    simp only [Prod.snd_add, Prod.fst_add, Submodule.coe_add, fv_add, hp, hq]
    rw [← Matrix.mulVec_add, smul_add]
    congr 1
    abel
  smul_mem' := by
    rintro c p ⟨w, hw, hp⟩
    refine ⟨_, smul_mem_hat L c hw, ?_⟩
    simp only [Prod.smul_snd, Prod.smul_fst, Submodule.coe_smul, fv_smul, hp]
    rw [← Matrix.mulVec_smul, smul_add, smul_comm]

end GlobalTheory.AdLat.Tower

open GlobalTheory.AdLat.Tower in
/- English proof (translation)
Introduce `F E _ _ _ _ _ n L g Λ hL hsp hΛ`. Take `⟨Λ', h1, hΛfg, hΛsp, hhat⟩` from `GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate F E n L g hL hsp`. Take `rfl : Λ = Λ'` from `SetLike.coe_injective (hΛ.trans h1.symm)`. Take `⟨hLc, hLa, -, -⟩` from `GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n L hL hsp`. Take `⟨hΛc, hΛa, -, -⟩` from `GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n Λ hΛfg hΛsp`.

Use `set G : Matrix (Fin n) (Fin n) (RA F E) := g.val with hG`. Establish `hto : ∀ u ∈ hat F (L : Set (Fin n → E)), G *ᵥ u ∈ hat F (Λ : Set (Fin n → E))`. Introduce `u hu`. Rewrite using `[← SetLike.mem_coe, hhat]`. Conclude with `⟨u, hu, rfl⟩`.

Establish `hfrom : ∀ z ∈ hat F (Λ : Set (Fin n → E)), ∃ u ∈ hat F (L : Set (Fin n → E)), G *ᵥ u = z`. Introduce `z hz`. Rewrite `hz` using `[← SetLike.mem_coe, hhat]`. Conclude with `hz`. Establish `hinj : ∀ u u' : Fin n → RA F E, G *ᵥ u = G *ᵥ u' → u = u'`.

Introduce `u u' h`. Use `congrArg (fun t => ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ t) h` as an intermediate fact. Simplify using `only [hG, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this`. Conclude with `this`. Use `haveI := projective_of_fg L hL`.

Establish `key : ∀ N : ℕ, ∃ f : L →ₗ[𝓞 E] Λ, 0 < N → ∀ a : L, ∃ w ∈ hat F (L : Set (Fin n → E)), fv F (f a : Fin n → E) = G *ᵥ (fv F (a : Fin n → E) + N • w)`. Introduce `N`. Break down `Nat.eq_zero_or_pos N with h0 | hN` into its components or cases. Conclude with `⟨0, fun h => absurd h (by omega)⟩`. Establish `hsurj : Function.Surjective ((LinearMap.fst (𝓞 E) L Λ).comp (rel L Λ G N).subtype)`.

Introduce `a`. Take `⟨x, hx, w, hw, e⟩` from `hΛa N hN _ (hto _ ((hLc a).2 a.2))`. Take `⟨u, hu, rfl⟩` from `hfrom w hw`. Use `⟨⟨(a, ⟨x, hx⟩), -u, neg_mem hu, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_add, mulVec_nsmul, Matrix.mulVec_neg, e]`.

Simplify using the standard rewrite rules. Take `⟨s, hs⟩` from `Module.projective_lifting_property _ LinearMap.id hsurj`. Use `⟨(LinearMap.snd (𝓞 E) L Λ).comp ((rel L Λ G N).subtype.comp s), fun _ a => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, e⟩` from `(s a).2`. Establish `ha : (s a).1.1 = a` using `LinearMap.congr_fun hs a`.

Rewrite `e` using `[ha]`. Conclude with `⟨w, hw, e⟩`. Use `choose f hf using key`. Use `⟨f, hf, ?_, ?_⟩` and prove the remaining obligations. Introduce `N m hN hm a`.

Take `⟨w, hw, e⟩` from `hf N hN a`. Take `⟨w', hw', e'⟩` from `hf (N * m) (Nat.mul_pos hN hm) a`. Take `⟨v, hv⟩` from `exists_div hΛc hN (f (N * m) a - f N a) (hto _ (sub_mem (nsmul_mem hw' m) hw)) (by`. Rewrite using `[Submodule.coe_sub, fv_sub, e, e', ← mulVec_nsmul, ← Matrix.mulVec_sub, smul_sub, mul_smul]`. Use `congr 1`.

Use the proof step `abel)`. Conclude with `⟨v, by rw [← hv]; abel⟩`. Introduce `N hN`. Use `⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨v, hv⟩`.

Take `⟨w, hw, e⟩` from `hf N hN a`. Take `⟨u, hu, eu⟩` from `hfrom _ ((hΛc v).2 v.2)`. Establish `e2 : fv F (f N a : Fin n → E) = G *ᵥ (N • u)`. Rewrite using `[mulVec_nsmul, eu, ← fv_nsmul, hv]`. Both sides reduce to the same expression.

Establish `e3` using `hinj _ _ (e.symm.trans e2)`. Conclude with `exists_div hLc hN a (sub_mem hu hw) (by rw [smul_sub, ← e3]; abel)`. Introduce and unpack `⟨v, rfl⟩`. Conclude with `⟨f N v, map_nsmul _ _ _⟩`. Take `⟨u, hu, eu⟩` from `hfrom _ ((hΛc a').2 a'.2)`.

Take `⟨x, hx, w, hw, rfl⟩` from `hLa N hN u hu`. Take `⟨w', hw', e'⟩` from `hf N hN ⟨x, hx⟩`. Take `⟨v, hv⟩` from `exists_div hΛc hN (a' - f N ⟨x, hx⟩) (hto _ (sub_mem hw hw')) (by`. Rewrite using `[Submodule.coe_sub, fv_sub, ← eu, e', ← mulVec_nsmul, ← Matrix.mulVec_sub, smul_sub]`. Use `congr 1`.

Use the proof step `abel)`. Conclude with `⟨⟨x, hx⟩, v, by rw [← hv]; abel⟩`.
-/
theorem GlobalTheory.AdLat.exists_linear_approx_tower : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)) (Λ : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (Λ : Set (Fin n → E)) = latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L → ∃ f : ℕ → (L →ₗ[𝓞 E] Λ), (∀ N : ℕ, 0 < N → ∀ a : L, ∃ w ∈ (hat F (L : Set (Fin n → E))), fv F (f N a : Fin n → E) = (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ (fv F (a : Fin n → E) + N • w)) ∧ (∀ N m : ℕ, 0 < N → 0 < m → ∀ a, ∃ v, f (N * m) a = f N a + N • v) ∧ ∀ N : ℕ, 0 < N → (∀ a, (∃ v, f N a = N • v) ↔ ∃ v, a = N • v) ∧ ∀ a', ∃ a v, a' = f N a + N • v := by
  intro F E _ _ _ _ _ n L g Λ hL hsp hΛ
  obtain ⟨Λ', h1, hΛfg, hΛsp, hhat⟩ := GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate F E n L g hL hsp
  obtain rfl : Λ = Λ' := SetLike.coe_injective (hΛ.trans h1.symm)
  obtain ⟨hLc, hLa, -, -⟩ := GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n L hL hsp
  obtain ⟨hΛc, hΛa, -, -⟩ := GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n Λ hΛfg hΛsp
  set G : Matrix (Fin n) (Fin n) (RA F E) := g.val with hG
  have hto : ∀ u ∈ hat F (L : Set (Fin n → E)), G *ᵥ u ∈ hat F (Λ : Set (Fin n → E)) := by
    intro u hu
    rw [← SetLike.mem_coe, hhat]
    exact ⟨u, hu, rfl⟩
  have hfrom : ∀ z ∈ hat F (Λ : Set (Fin n → E)), ∃ u ∈ hat F (L : Set (Fin n → E)), G *ᵥ u = z := by
    intro z hz
    rw [← SetLike.mem_coe, hhat] at hz
    exact hz
  have hinj : ∀ u u' : Fin n → RA F E, G *ᵥ u = G *ᵥ u' → u = u' := by
    intro u u' h
    have := congrArg (fun t => ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ t) h
    simp only [hG, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
    exact this
  haveI := projective_of_fg L hL
  have key : ∀ N : ℕ, ∃ f : L →ₗ[𝓞 E] Λ, 0 < N → ∀ a : L, ∃ w ∈ hat F (L : Set (Fin n → E)),
      fv F (f a : Fin n → E) = G *ᵥ (fv F (a : Fin n → E) + N • w) := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · exact ⟨0, fun h => absurd h (by omega)⟩
    have hsurj : Function.Surjective
        ((LinearMap.fst (𝓞 E) L Λ).comp (rel L Λ G N).subtype) := by
      intro a
      obtain ⟨x, hx, w, hw, e⟩ := hΛa N hN _ (hto _ ((hLc a).2 a.2))
      obtain ⟨u, hu, rfl⟩ := hfrom w hw
      refine ⟨⟨(a, ⟨x, hx⟩), -u, neg_mem hu, ?_⟩, rfl⟩
      rw [Matrix.mulVec_add, mulVec_nsmul, Matrix.mulVec_neg, e]
      simp
    obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hsurj
    refine ⟨(LinearMap.snd (𝓞 E) L Λ).comp ((rel L Λ G N).subtype.comp s), fun _ a => ?_⟩
    obtain ⟨w, hw, e⟩ := (s a).2
    have ha : (s a).1.1 = a := LinearMap.congr_fun hs a
    rw [ha] at e
    exact ⟨w, hw, e⟩
  choose f hf using key
  refine ⟨f, hf, ?_, ?_⟩
  · intro N m hN hm a
    obtain ⟨w, hw, e⟩ := hf N hN a
    obtain ⟨w', hw', e'⟩ := hf (N * m) (Nat.mul_pos hN hm) a
    obtain ⟨v, hv⟩ := exists_div hΛc hN (f (N * m) a - f N a)
      (hto _ (sub_mem (nsmul_mem hw' m) hw)) (by
        rw [Submodule.coe_sub, fv_sub, e, e', ← mulVec_nsmul, ← Matrix.mulVec_sub, smul_sub,
          mul_smul]
        congr 1
        abel)
    exact ⟨v, by rw [← hv]; abel⟩
  · intro N hN
    refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
    · rintro ⟨v, hv⟩
      obtain ⟨w, hw, e⟩ := hf N hN a
      obtain ⟨u, hu, eu⟩ := hfrom _ ((hΛc v).2 v.2)
      have e2 : fv F (f N a : Fin n → E) = G *ᵥ (N • u) := by
        rw [mulVec_nsmul, eu, ← fv_nsmul, hv]; rfl
      have e3 := hinj _ _ (e.symm.trans e2)
      exact exists_div hLc hN a (sub_mem hu hw) (by rw [smul_sub, ← e3]; abel)
    · rintro ⟨v, rfl⟩
      exact ⟨f N v, map_nsmul _ _ _⟩
    · obtain ⟨u, hu, eu⟩ := hfrom _ ((hΛc a').2 a'.2)
      obtain ⟨x, hx, w, hw, rfl⟩ := hLa N hN u hu
      obtain ⟨w', hw', e'⟩ := hf N hN ⟨x, hx⟩
      obtain ⟨v, hv⟩ := exists_div hΛc hN (a' - f N ⟨x, hx⟩) (hto _ (sub_mem hw hw')) (by
        rw [Submodule.coe_sub, fv_sub, ← eu, e', ← mulVec_nsmul, ← Matrix.mulVec_sub, smul_sub]
        congr 1
        abel)
      exact ⟨⟨x, hx⟩, v, by rw [← hv]; abel⟩
