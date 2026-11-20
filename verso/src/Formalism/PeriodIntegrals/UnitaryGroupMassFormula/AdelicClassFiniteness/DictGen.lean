import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictPlan

noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix

namespace DictGen

variable (I : AutInst)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lf_eq : I.Lf = Submodule.span (IntAf I.F I.E)
    (Set.range fun x : I.L => iv I (x : Fin I.n → I.E)) := rfl

/- English proof (translation)
Rewrite using `[lf_eq]`. Conclude with `Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩`.
-/
theorem iv_mem {l : Fin I.n → I.E} (hl : l ∈ I.L) : iv I l ∈ I.Lf := by
  rw [lf_eq]
  exact Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩

/- English proof (translation)
Use `first`. Consider the case `rw [Nat.cast_smul_eq_nsmul (I.E ⊗[I.F] Af I.F)]`. Conclude with `nsmul_mem hw k`. Consider the case `rw [Nat.cast_smul_eq_nsmul]`. Conclude with `nsmul_mem hw k`.

Consider the case `exact I.Lf.smul_mem (k : IntAf I.F I.E) hw`.
-/
theorem natSmul_mem (k : ℕ) {w : Fin I.n → I.E ⊗[I.F] Af I.F} (hw : w ∈ I.Lf) :
    (k : I.E ⊗[I.F] Af I.F) • w ∈ I.Lf := by
  first
    | rw [Nat.cast_smul_eq_nsmul (I.E ⊗[I.F] Af I.F)]
      exact nsmul_mem hw k
    | rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem hw k
    | exact I.Lf.smul_mem (k : IntAf I.F I.E) hw

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `first`. Consider the case `simp [iv, nsmul_eq_mul]`. Consider the case `simp only [iv, Pi.smul_apply, map_nsmul, nsmul_eq_mul, smul_eq_mul]`.
-/
theorem iv_nsmul (N : ℕ) (v : Fin I.n → I.E) :
    iv I (N • v) = (N : I.E ⊗[I.F] Af I.F) • iv I v := by
  funext i
  first
    | simp [iv, nsmul_eq_mul]
    | simp only [iv, Pi.smul_apply, map_nsmul, nsmul_eq_mul, smul_eq_mul]

/- English proof (translation)
Establish `hu : IsUnit (N : (I.E ⊗[I.F] Af I.F))`. Establish `h0 : (N : I.F) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `h1` using `(IsUnit.mk0 _ h0).map (algebraMap I.F (I.E ⊗[I.F] Af I.F))`. Rewrite `h1` using `[map_natCast]`. Then use the resulting hypothesis. Use function extensionality and compare the values at `i`.

Establish `hi` using `congrFun h i`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at hi`. Conclude with `hu.mul_left_cancel hi`.
-/
theorem natCast_cancel (N : ℕ) (hN : 0 < N) {a b : Fin I.n → I.E ⊗[I.F] Af I.F}
    (h : (N : I.E ⊗[I.F] Af I.F) • a = (N : I.E ⊗[I.F] Af I.F) • b) : a = b := by
  have hu : IsUnit (N : (I.E ⊗[I.F] Af I.F)) := by
    have h0 : (N : I.F) ≠ 0 := by exact_mod_cast hN.ne'
    have h1 := (IsUnit.mk0 _ h0).map (algebraMap I.F (I.E ⊗[I.F] Af I.F))
    rwa [map_natCast] at h1
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact hu.mul_left_cancel hi

/- English proof (translation)
Use `first`. Consider the case `exact Units.mul_inv (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))`. Consider the case `simp`.
-/
theorem fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  first
    | exact Units.mul_inv (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
    | simp

/- English proof (translation)
Use `first`. Consider the case `exact Units.inv_mul (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))`. Consider the case `simp`.
-/
theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  first
    | exact Units.inv_mul (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
    | simp

def lamM (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Submodule (𝓞 I.E) (Fin I.n → I.E) where
  carrier := {v | M *ᵥ iv I v ∈ I.Lf}
  add_mem' := fun {v w} hv hw => by
    have e : iv I (v + w) = iv I v + iv I w := by
      funext i; simp [iv]
    show M *ᵥ iv I (v + w) ∈ I.Lf
    rw [e, Matrix.mulVec_add]
    exact I.Lf.add_mem hv hw
  zero_mem' := by
    have e : iv I (0 : Fin I.n → I.E) = 0 := by
      funext i; simp [iv]
    show M *ᵥ iv I 0 ∈ I.Lf
    rw [e, Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  smul_mem' := fun a v hv => by
    have ha : Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) ∈ IntAf I.F I.E :=
      Subring.subset_closure (Or.inl ⟨⟨(a : I.E), a, rfl⟩, rfl⟩)
    have e : iv I (a • v) = Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) • iv I v := by
      funext i
      simp [iv, Algebra.smul_def]
    show M *ᵥ iv I (a • v) ∈ I.Lf
    rw [e, Matrix.mulVec_smul]
    exact I.Lf.smul_mem ⟨_, ha⟩ hv

/- English proof (translation)
Introduce `y hy`. Rewrite `hy` using `[lf_eq]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨⟨l, hl⟩, rfl⟩` from `hz`.

Conclude with `(show M *ᵥ iv I l ∈ I.Lf from h hl)`. Consider the case `zero`. Rewrite using `[Matrix.mulVec_zero]`. Conclude with `I.Lf.zero_mem`. Consider the case `add a b _ _ ha hb`.

Rewrite using `[Matrix.mulVec_add]`. Conclude with `I.Lf.add_mem ha hb`. Consider the case `smul s a _ ha`. Establish `e : M *ᵥ (s • a) = s • (M *ᵥ a)` using `by show M *ᵥ ((s : (I.E ⊗[I.F] Af I.F)) • a) = (s : (I.E ⊗[I.F] Af I.F)) • (M *ᵥ a)`. Conclude with `Matrix.mulVec_smul M _ a`.

Rewrite using `[e]`. Conclude with `I.Lf.smul_mem s ha`.
-/
theorem mulVec_mem_of_le {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (h : I.L ≤ lamM I M) :
    ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf := by
  intro y hy
  rw [lf_eq] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hz
    exact (show M *ᵥ iv I l ∈ I.Lf from h hl)
  | zero =>
    rw [Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  | add a b _ _ ha hb =>
    rw [Matrix.mulVec_add]
    exact I.Lf.add_mem ha hb
  | smul s a _ ha =>
    have e : M *ᵥ (s • a) = s • (M *ᵥ a) := by
      show M *ᵥ ((s : (I.E ⊗[I.F] Af I.F)) • a) = (s : (I.E ⊗[I.F] Af I.F)) • (M *ᵥ a)
      exact Matrix.mulVec_smul M _ a
    rw [e]
    exact I.Lf.smul_mem s ha

/- English proof (translation)
Use `first`. Consider the case `exact Matrix.smul_mulVec c M y`. Consider the case `exact Matrix.smul_mulVec_assoc c M y`. Consider the case `(ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])`.
-/
private theorem smul_mulVec_lemma {A : Type} [CommRing A] {n : ℕ} (c : A)
    (M : Matrix (Fin n) (Fin n) A) (y : Fin n → A) : (c • M) *ᵥ y = c • (M *ᵥ y) := by
  first
    | exact Matrix.smul_mulVec c M y
    | exact Matrix.smul_mulVec_assoc c M y
    | (ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])

/- English proof (translation)
Take `⟨s, hs⟩` from `I.L_fg`. Use `choose m hm0 hm using fun v : Fin I.n → I.E => hD I (M *ᵥ iv I v)`. Use `⟨∏ j ∈ s, m j, Finset.prod_pos fun j _ => hm0 j, ?_⟩` and prove the remaining obligations. Establish `hle : I.L ≤ lamM I (((∏ j ∈ s, m j : ℕ) : (I.E ⊗[I.F] Af I.F)) • M)`. Rewrite using `[← hs, Submodule.span_le]`.

Introduce `v hv`. Use `show (((∏ j ∈ s, m j : ℕ) : (I.E ⊗[I.F] Af I.F)) • M) *ᵥ iv I v ∈ I.Lf`. Rewrite using `[smul_mulVec_lemma, ← Finset.prod_erase_mul s m hv, Nat.cast_mul, mul_smul]`. Conclude with `natSmul_mem I _ (hm v)`. Introduce `y hy`.

Establish `h2` using `mulVec_mem_of_le I hle y hy`. Rewrite `h2` using `[smul_mulVec_lemma]`. Then use the resulting hypothesis.
-/
theorem denom (hD : LDenom) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ y ∈ I.Lf, (N : I.E ⊗[I.F] Af I.F) • (M *ᵥ y) ∈ I.Lf := by
  classical
  obtain ⟨s, hs⟩ := I.L_fg
  choose m hm0 hm using fun v : Fin I.n → I.E => hD I (M *ᵥ iv I v)
  refine ⟨∏ j ∈ s, m j, Finset.prod_pos fun j _ => hm0 j, ?_⟩
  have hle : I.L ≤ lamM I (((∏ j ∈ s, m j : ℕ) : (I.E ⊗[I.F] Af I.F)) • M) := by
    rw [← hs, Submodule.span_le]
    intro v hv
    show (((∏ j ∈ s, m j : ℕ) : (I.E ⊗[I.F] Af I.F)) • M) *ᵥ iv I v ∈ I.Lf
    rw [smul_mulVec_lemma, ← Finset.prod_erase_mul s m hv, Nat.cast_mul, mul_smul]
    exact natSmul_mem I _ (hm v)
  intro y hy
  have h2 := mulVec_mem_of_le I hle y hy
  rwa [smul_mulVec_lemma] at h2

/- English proof (translation)
Take `⟨N1, h1, hN1⟩` from `denom I hD (I.fmat x)`. Take `⟨N2, h2, hN2⟩` from `denom I hD (I.fmat x⁻¹)`. Use `⟨N1 * N2, Nat.mul_pos h1 h2, fun y hy => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, mul_comm, mul_smul]`. Conclude with `natSmul_mem I _ (hN1 y hy)`.

Rewrite using `[Nat.cast_mul, mul_smul]`. Conclude with `natSmul_mem I _ (hN2 y hy)`.
-/
theorem exists_denominator_fmat (hD : LDenom) (x : I.Gf) : ∃ N : ℕ, 0 < N ∧ ∀ y ∈ I.Lf,
    (N : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ y) ∈ I.Lf ∧
      (N : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ y) ∈ I.Lf := by
  obtain ⟨N1, h1, hN1⟩ := denom I hD (I.fmat x)
  obtain ⟨N2, h2, hN2⟩ := denom I hD (I.fmat x⁻¹)
  refine ⟨N1 * N2, Nat.mul_pos h1 h2, fun y hy => ⟨?_, ?_⟩⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact natSmul_mem I _ (hN1 y hy)
  · rw [Nat.cast_mul, mul_smul]
    exact natSmul_mem I _ (hN2 y hy)

/- English proof (translation)
Use `show I.fmat x⁻¹ *ᵥ iv I (N • l) ∈ I.Lf`. Rewrite using `[iv_nsmul, Matrix.mulVec_smul]`. Conclude with `(hN _ (iv_mem I hl)).2`.
-/
theorem nL_sub (x : I.Gf) (N : ℕ)
    (hN : ∀ y ∈ I.Lf, (N : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ y) ∈ I.Lf ∧
      (N : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ y) ∈ I.Lf)
    {l : Fin I.n → I.E} (hl : l ∈ I.L) : N • l ∈ abelian₂ I x := by
  show I.fmat x⁻¹ *ᵥ iv I (N • l) ∈ I.Lf
  rw [iv_nsmul, Matrix.mulVec_smul]
  exact (hN _ (iv_mem I hl)).2

/- English proof (translation)
Apply `hInt I` to reduce the goal to its premises. Establish `hv' : I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf` using `hv`. Establish `e : iv I v = I.fmat x *ᵥ (I.fmat x⁻¹ *ᵥ iv I v)`. Rewrite using `[Matrix.mulVec_mulVec, fmat_mul_inv, Matrix.one_mulVec]`. Rewrite using `[iv_nsmul, e]`.

Conclude with `(hN _ hv').1`.
-/
theorem nLam_sub (hInt : LInter) (x : I.Gf) (N : ℕ)
    (hN : ∀ y ∈ I.Lf, (N : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ y) ∈ I.Lf ∧
      (N : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ y) ∈ I.Lf)
    {v : Fin I.n → I.E} (hv : v ∈ abelian₂ I x) : N • v ∈ I.L := by
  apply hInt I
  have hv' : I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf := hv
  have e : iv I v = I.fmat x *ᵥ (I.fmat x⁻¹ *ᵥ iv I v) := by
    rw [Matrix.mulVec_mulVec, fmat_mul_inv, Matrix.one_mulVec]
  rw [iv_nsmul, e]
  exact (hN _ hv').1

end DictGen

/- English proof (translation)
Introduce `I x`. Take `⟨N, hN, hN'⟩` from `DictGen.exists_denominator_fmat I hD x`. Establish `hNE : (N : I.E) ≠ 0` using `by exact_mod_cast hN.ne'`. Prove the components needed by the constructor for the conclusion. Set `ψ : (Fin I.n → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E)` to `(((N : I.E)⁻¹ • LinearMap.id : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E))).restrictScalars (𝓞 I.E)`.

Establish `hle : abelian₂ I x ≤ I.L.map ψ`. Introduce `v hv`. Establish `h1 : N • v ∈ I.L` using `DictGen.nLam_sub I hInt x N hN' hv`. Establish `e : ψ (N • v) = v` using `by show (N : I.E)⁻¹ • (N • v) = v`. Rewrite using `[← Nat.cast_smul_eq_nsmul I.E, smul_smul, inv_mul_cancel₀ hNE, one_smul]`.

Rewrite using `[← e]`. Conclude with `Submodule.mem_map_of_mem h1`. Use `haveI : IsNoetherian (𝓞 I.E) (I.L.map ψ) := isNoetherian_of_fg_of_noetherian _ (I.L_fg.map ψ)`. Use `haveI : IsNoetherian (𝓞 I.E) (abelian₂ I x) := isNoetherian_of_le hle`. Use `first`.

Consider the case `exact (Submodule.fg_top _).mp (IsNoetherian.noetherian _)`. Consider the case `exact Module.Finite.iff_fg.mp inferInstance`. Rewrite using `[eq_top_iff, ← I.L_span, Submodule.span_le]`. Introduce `v hv`. Establish `h1 : N • v ∈ abelian₂ I x` using `DictGen.nL_sub I x N hN' hv`.

Establish `h2 : N • v ∈ Submodule.span I.E ((abelian₂ I x : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Fin I.n → I.E))` using `Submodule.subset_span h1`. Establish `e : v = (N : I.E)⁻¹ • (N • v)`. Rewrite using `[← Nat.cast_smul_eq_nsmul I.E, smul_smul, inv_mul_cancel₀ hNE, one_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ h2`.
-/
theorem mLat_of (hInt : LInter) (hD : LDenom) : MLat := by
  intro I x
  obtain ⟨N, hN, hN'⟩ := DictGen.exists_denominator_fmat I hD x
  have hNE : (N : I.E) ≠ 0 := by exact_mod_cast hN.ne'
  constructor
  · let ψ : (Fin I.n → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E) :=
      (((N : I.E)⁻¹ • LinearMap.id : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E))).restrictScalars (𝓞 I.E)
    have hle : abelian₂ I x ≤ I.L.map ψ := by
      intro v hv
      have h1 : N • v ∈ I.L := DictGen.nLam_sub I hInt x N hN' hv
      have e : ψ (N • v) = v := by
        show (N : I.E)⁻¹ • (N • v) = v
        rw [← Nat.cast_smul_eq_nsmul I.E, smul_smul, inv_mul_cancel₀ hNE, one_smul]
      rw [← e]
      exact Submodule.mem_map_of_mem h1
    haveI : IsNoetherian (𝓞 I.E) (I.L.map ψ) := isNoetherian_of_fg_of_noetherian _ (I.L_fg.map ψ)
    haveI : IsNoetherian (𝓞 I.E) (abelian₂ I x) := isNoetherian_of_le hle
    first
      | exact (Submodule.fg_top _).mp (IsNoetherian.noetherian _)
      | exact Module.Finite.iff_fg.mp inferInstance
  · rw [eq_top_iff, ← I.L_span, Submodule.span_le]
    intro v hv
    have h1 : N • v ∈ abelian₂ I x := DictGen.nL_sub I x N hN' hv
    have h2 : N • v ∈ Submodule.span I.E
        ((abelian₂ I x : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Fin I.n → I.E)) :=
      Submodule.subset_span h1
    have e : v = (N : I.E)⁻¹ • (N • v) := by
      rw [← Nat.cast_smul_eq_nsmul I.E, smul_smul, inv_mul_cancel₀ hNE, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ h2

/- English proof (translation)
Introduce `I x y hy`. Take `⟨N, hN, hN'⟩` from `DictGen.exists_denominator_fmat I hD x`. Establish `hNE : (N : I.E) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hNL : ∀ u ∈ I.Lf, (N : (I.E ⊗[I.F] Af I.F)) • u ∈ Submodule.span (IntAf I.F I.E) (Set.range fun v : abelian₂ I x => iv I (v : Fin I.n → I.E))`. Introduce `u hu`.

Rewrite `hu` using `[DictGen.lf_eq]`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨⟨l, hl⟩, rfl⟩` from `hz`. Use `show (N : (I.E ⊗[I.F] Af I.F)) • iv I l ∈ _`.

Rewrite using `[← DictGen.iv_nsmul]`. Conclude with `Submodule.subset_span ⟨⟨N • l, DictGen.nL_sub I x N hN' hl⟩, rfl⟩`. Consider the case `zero`. Rewrite using `[smul_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add a b _ _ ha hb`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul s a _ ha`. Establish `e : (N : (I.E ⊗[I.F] Af I.F)) • (s • a) = s • ((N : (I.E ⊗[I.F] Af I.F)) • a)` using `by show (N : (I.E ⊗[I.F] Af I.F)) • ((s : (I.E ⊗[I.F] Af I.F)) • a) = (s : (I.E ⊗[I.F] Af I.F)) • ((N : (I.E ⊗[I.F] Af I.F)) • a)`.

Rewrite using `[smul_smul, smul_smul, mul_comm]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ s ha`. Take `⟨l, hl, y', hy', hw⟩` from `hDen I (N * N) (Nat.mul_pos hN hN) _ (hN' y hy).1`. Take `⟨v, hv⟩ : ∃ v : Fin I.n → I.E, v = (N : I.E)⁻¹ • l` from `⟨_, rfl⟩`.

Establish `hNv : N • v = l`. Rewrite using `[hv, ← Nat.cast_smul_eq_nsmul I.E, smul_smul, mul_inv_cancel₀ hNE, one_smul]`. Establish `hz : I.fmat x *ᵥ y = iv I v + (N : (I.E ⊗[I.F] Af I.F)) • y'`. Apply `DictGen.natCast_cancel I N hN` to reduce the goal to its premises. Rewrite using `[smul_add, ← DictGen.iv_nsmul, hNv, hw, smul_smul, Nat.cast_mul]`.

Establish `hvL : v ∈ abelian₂ I x` using `by show I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf`. Establish `e : iv I v = I.fmat x *ᵥ y - (N : (I.E ⊗[I.F] Af I.F)) • y'` using `by first`. Consider the case `rw [hz, add_sub_cancel_right]`. Consider the case `(rw [hz]; abel)`. Rewrite using `[e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, DictGen.fmat_inv_mul, Matrix.one_mulVec, Matrix.mulVec_smul]`.

Conclude with `I.Lf.sub_mem hy (hN' y' hy').2`. Rewrite using `[hz]`. Conclude with `Submodule.add_mem _ (Submodule.subset_span ⟨⟨v, hvL⟩, rfl⟩) (hNL y' hy')`.
-/
theorem mGen_of (hD : LDenom) (hDen : LDense) : MGen := by
  intro I x y hy
  obtain ⟨N, hN, hN'⟩ := DictGen.exists_denominator_fmat I hD x
  have hNE : (N : I.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNL : ∀ u ∈ I.Lf, (N : (I.E ⊗[I.F] Af I.F)) • u ∈
      Submodule.span (IntAf I.F I.E) (Set.range fun v : abelian₂ I x => iv I (v : Fin I.n → I.E)) := by
    intro u hu
    rw [DictGen.lf_eq] at hu
    induction hu using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨l, hl⟩, rfl⟩ := hz
      show (N : (I.E ⊗[I.F] Af I.F)) • iv I l ∈ _
      rw [← DictGen.iv_nsmul]
      exact Submodule.subset_span ⟨⟨N • l, DictGen.nL_sub I x N hN' hl⟩, rfl⟩
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [smul_add]
      exact Submodule.add_mem _ ha hb
    | smul s a _ ha =>
      have e : (N : (I.E ⊗[I.F] Af I.F)) • (s • a) = s • ((N : (I.E ⊗[I.F] Af I.F)) • a) := by
        show (N : (I.E ⊗[I.F] Af I.F)) • ((s : (I.E ⊗[I.F] Af I.F)) • a) = (s : (I.E ⊗[I.F] Af I.F)) • ((N : (I.E ⊗[I.F] Af I.F)) • a)
        rw [smul_smul, smul_smul, mul_comm]
      rw [e]
      exact Submodule.smul_mem _ s ha
  obtain ⟨l, hl, y', hy', hw⟩ := hDen I (N * N) (Nat.mul_pos hN hN) _ (hN' y hy).1
  obtain ⟨v, hv⟩ : ∃ v : Fin I.n → I.E, v = (N : I.E)⁻¹ • l := ⟨_, rfl⟩
  have hNv : N • v = l := by
    rw [hv, ← Nat.cast_smul_eq_nsmul I.E, smul_smul, mul_inv_cancel₀ hNE, one_smul]
  have hz : I.fmat x *ᵥ y = iv I v + (N : (I.E ⊗[I.F] Af I.F)) • y' := by
    apply DictGen.natCast_cancel I N hN
    rw [smul_add, ← DictGen.iv_nsmul, hNv, hw, smul_smul, Nat.cast_mul]
  have hvL : v ∈ abelian₂ I x := by
    show I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf
    have e : iv I v = I.fmat x *ᵥ y - (N : (I.E ⊗[I.F] Af I.F)) • y' := by
      first
        | rw [hz, add_sub_cancel_right]
        | (rw [hz]; abel)
    rw [e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, DictGen.fmat_inv_mul, Matrix.one_mulVec,
      Matrix.mulVec_smul]
    exact I.Lf.sub_mem hy (hN' y' hy').2
  rw [hz]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨⟨v, hvL⟩, rfl⟩) (hNL y' hy')

end PIW.AdelClassFin
