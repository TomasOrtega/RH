import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LocRho
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundTheorem
import Development.AbelianVarietyTheory.Definitions.Divisors.WtSizeOver

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open GlobalTheory.CongW (IntMat wtSize HasTypeVec IsIntegralOpW OverPair wtSizeOver)

namespace UpperTheory.Gal.Gen.Loc

/- English proof (translation)
Establish `hvl : Valued.v ((l : ℕ) : u.adicCompletion E) < 1`. Establish `h1 : u.valuation E (((l : ℕ) : 𝓞 E) : E) < 1` using `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) u _).2 hl`. Establish `h2 : (((l : ℕ) : u.adicCompletion E)) = algebraMap E (u.adicCompletion E) (((l : ℕ) : 𝓞 E) : E)` using `by simp`. Rewrite using `[h2]`. Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _).trans_lt h1`.

Establish `hlnorm : ‖j ((l : ℕ) : u.adicCompletion E)‖ = (l : ℝ)⁻¹`. Establish `h0 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[map_natCast, h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l]), Padic.norm_p]`. Establish `hlt : ∀ k : ℕ, ‖j ((l : ℕ) : u.adicCompletion E)‖ * ‖j y‖ ^ k < 1`. Introduce `k`.

Establish `hyv : Valued.v y ≤ 1` using `hy`. Establish `hv : Valued.v (((l : ℕ) : u.adicCompletion E) * y ^ k) < 1`. Rewrite using `[map_mul, map_pow]`. Conclude with `mul_lt_one_of_lt_of_le hvl (pow_le_one' hyv k)`. Establish `ht` using `Valued.tendsto_zero_pow_of_v_lt_one hv`.

Establish `ht2 : Filter.Tendsto (fun m : ℕ => (j (((l : ℕ) : u.adicCompletion E) * y ^ k)) ^ m) Filter.atTop (nhds 0)`. Use `(hj.tendsto 0).comp ht` as an intermediate fact. Simplify `this` using `[Function.comp_def, map_pow]`. Use `tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ht2` as an intermediate fact. Simplify `this` using `[map_mul, map_pow, norm_mul, norm_pow]`.

Assume the negation of the conclusion as `hcon`. Establish `hgt : 1 < ‖j y‖` using `not_le.1 hcon`. Establish `hlpos : 0 < ‖j ((l : ℕ) : u.adicCompletion E)‖`. Rewrite using `[hlnorm]`. Conclude with `inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)`.

Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (‖j ((l : ℕ) : u.adicCompletion E)‖⁻¹) hgt`. Use `hlt k` as an intermediate fact. Establish `h3 : 1 < ‖j ((l : ℕ) : u.adicCompletion E)‖ * ‖j y‖ ^ k`. Rewrite `hk` using `[inv_lt_iff_one_lt_mul₀ hlpos]`. Conclude with `hk.trans_eq (mul_comm _ _)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_map_integer_le_one {E : Type} [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (u : HeightOneSpectrum (𝓞 E)) (j : u.adicCompletion E →+* Qbar l) (hl : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (hj : Continuous j) (y : u.adicCompletion E) (hy : y ∈ u.adicCompletionIntegers E) : ‖j y‖ ≤ 1 := by
  have hvl : Valued.v ((l : ℕ) : u.adicCompletion E) < 1 := by
    have h1 : u.valuation E (((l : ℕ) : 𝓞 E) : E) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) u _).2 hl
    have h2 : (((l : ℕ) : u.adicCompletion E)) = algebraMap E (u.adicCompletion E) (((l : ℕ) : 𝓞 E) : E) := by simp
    rw [h2]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _).trans_lt h1
  have hlnorm : ‖j ((l : ℕ) : u.adicCompletion E)‖ = (l : ℝ)⁻¹ := by
    have h0 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [map_natCast, h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l]), Padic.norm_p]
  have hlt : ∀ k : ℕ, ‖j ((l : ℕ) : u.adicCompletion E)‖ * ‖j y‖ ^ k < 1 := by
    intro k
    have hyv : Valued.v y ≤ 1 := hy
    have hv : Valued.v (((l : ℕ) : u.adicCompletion E) * y ^ k) < 1 := by
      rw [map_mul, map_pow]
      exact mul_lt_one_of_lt_of_le hvl (pow_le_one' hyv k)
    have ht := Valued.tendsto_zero_pow_of_v_lt_one hv
    have ht2 : Filter.Tendsto (fun m : ℕ => (j (((l : ℕ) : u.adicCompletion E) * y ^ k)) ^ m) Filter.atTop (nhds 0) := by
      have := (hj.tendsto 0).comp ht
      simpa [Function.comp_def, map_pow] using this
    have := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ht2
    simpa [map_mul, map_pow, norm_mul, norm_pow] using this
  by_contra hcon
  have hgt : 1 < ‖j y‖ := not_le.1 hcon
  have hlpos : 0 < ‖j ((l : ℕ) : u.adicCompletion E)‖ := by
    rw [hlnorm]
    exact inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖j ((l : ℕ) : u.adicCompletion E)‖⁻¹) hgt
  have := hlt k
  have h3 : 1 < ‖j ((l : ℕ) : u.adicCompletion E)‖ * ‖j y‖ ^ k := by
    rw [inv_lt_iff_one_lt_mul₀ hlpos] at hk
    exact hk.trans_eq (mul_comm _ _)
  linarith

/- English proof (translation)
Establish `h1` using `norm_map_integer_le_one l u j hl hj _ (hM a b)`. Establish `hlnorm : ‖j ((l : ℕ) : u.adicCompletion E)‖ = (l : ℝ)⁻¹`. Establish `h0 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[map_natCast, h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l]), Padic.norm_p]`. Establish `hl0 : (0 : ℝ) < (l : ℝ) ^ d` using `pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) d`.

Rewrite `h1` using `[Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, norm_mul, norm_pow, hlnorm, inv_pow]`. Rewrite `h1` using `[inv_mul_le_iff₀ hl0, mul_one]`. Then use the resulting hypothesis.
-/
theorem norm_map_entry_le {E : Type} [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] {n : ℕ}
    (u : HeightOneSpectrum (𝓞 E)) (j : u.adicCompletion E →+* Qbar l) (hl : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (hj : Continuous j) (d : ℕ) (M : Matrix (Fin n) (Fin n) (u.adicCompletion E))
    (hM : GlobalTheory.CongW.IntMat u (((l : u.adicCompletion E) ^ d) • M)) (a b : Fin n) : ‖j (M a b)‖ ≤ (l : ℝ) ^ d := by
  have h1 := norm_map_integer_le_one l u j hl hj _ (hM a b)
  have hlnorm : ‖j ((l : ℕ) : u.adicCompletion E)‖ = (l : ℝ)⁻¹ := by
    have h0 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [map_natCast, h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l]), Padic.norm_p]
  have hl0 : (0 : ℝ) < (l : ℝ) ^ d := pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) d
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, norm_mul, norm_pow, hlnorm, inv_pow] at h1
  rwa [inv_mul_le_iff₀ hl0, mul_one] at h1

/- English proof (translation)
Establish `hex` using `fun v : InfinitePlace E => GlobalTheory.LadicInf.exists_place E l (ι.symm.toRingHom.comp v.embedding)`. Use `choose u j hl hj hjE using hex`. Set `f : InfinitePlace E → Af E →+* ℂ` to `fun v => ι.toRingHom.comp ((j v).comp (pLoc E (u v)))`. Set `κ : UA E n →* (InfinitePlace E → GL (Fin n) ℂ)` to `MonoidHom.pi fun v => (Matrix.GeneralLinearGroup.map ((f v).comp (pFin E))).comp (UA E n).subtype`. Establish `hκ : ∀ (g : UA E n) (v : InfinitePlace E), κ g v = Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (j v)) (cLoc (u v) g)`.

Introduce `g v`. Use `ext`. Both sides reduce to the same expression. Use `⟨u, κ, fun v => ⟨hl v, fun x hx => ?_⟩, fun g v hg => by rw [hκ, hg, map_one], ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun φ : E →+* Qbar l => φ (x : E)) (hjE v)`.

Simplify using `only [RingHom.coe_comp, Function.comp_apply] at h`. Establish `hv : Valued.v (algebraMap E ((u v).adicCompletion E) (x : E)) < 1` using `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (u v) _).trans_lt ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) (u v) _).2 hx)`. Establish `ht` using `((hj v).tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one hv)`. Establish `ht2 : Filter.Tendsto (fun m : ℕ => (j v (algebraMap E ((u v).adicCompletion E) (x : E))) ^ m) Filter.atTop (nhds 0)`. Simplify `ht` using `[Function.comp_def, map_pow]`.

Use `tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ht2` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `this`. Introduce and unpack `γ ⟨g₀, hg₀⟩`. Use function extensionality and compare the values at `v`.

Use extensionality with `a b`. Express the relevant statement in the definitionally equal form `(f v) (pFin E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) a b)) = coord v.embedding (pInf E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) a b))`. Establish `hg₁ : (γ.1 : GL (Fin n) (Ad E)) = ratGL E n g₀` using `hg₀.symm`. Rewrite using `[hg₁]`. Express the relevant statement in the definitionally equal form `(f v) (pFin E (algebraMap E (Ad E) ((g₀ : Matrix (Fin n) (Fin n) E) a b))) = coord v.embedding (pInf E (algebraMap E (Ad E) ((g₀ : Matrix (Fin n) (Fin n) E) a b)))`.

Rewrite using `[coord_algebraMap]`. Establish `h` using `congrArg (fun φ : E →+* Qbar l => φ ((g₀ : Matrix (Fin n) (Fin n) E) a b)) (hjE v)`. Simplify using `only [RingHom.coe_comp, Function.comp_apply] at h`. Express the relevant statement in the definitionally equal form `ι (j v (algebraMap E (u v |>.adicCompletion E) _)) = _`. Rewrite using `[h]`.

Simplify using the standard rewrite rules. Introduce `x hx`. Use function extensionality and compare the values at `v`. Establish `hx' : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1` using `hx`. Establish `h2 : Matrix.GeneralLinearGroup.map ((f v).comp (pFin E)) x.1 = Matrix.GeneralLinearGroup.map (f v) (Matrix.GeneralLinearGroup.map (pFin E) x.1)` using `by ext; rfl`.

Express the relevant statement in the definitionally equal form `Matrix.GeneralLinearGroup.map ((f v).comp (pFin E)) x.1 = 1`. Rewrite using `[h2, hx', map_one]`. Introduce `g d hd v a b`. Take `⟨h1, h2⟩` from `hd (u v) (hl v)`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[hκ g v]`. Express the relevant statement in the definitionally equal form `‖ι.symm (ι (j v (((cLoc (u v) g : GL (Fin n) ((u v).adicCompletion E)) : Matrix (Fin n) (Fin n) ((u v).adicCompletion E)) a b)))‖ ≤ _`. Rewrite using `[RingEquiv.symm_apply_apply]`. Conclude with `norm_map_entry_le l (u v) (j v) (hl v) (hj v) d _ h1 a b`. Rewrite using `[hκ g v, ← map_inv]`.

Express the relevant statement in the definitionally equal form `‖ι.symm (ι (j v ((((cLoc (u v) g)⁻¹ : GL (Fin n) ((u v).adicCompletion E)) : Matrix (Fin n) (Fin n) ((u v).adicCompletion E)) a b)))‖ ≤ _`. Rewrite using `[RingEquiv.symm_apply_apply]`. Conclude with `norm_map_entry_le l (u v) (j v) (hl v) (hj v) d _ h2 a b`.
-/
theorem kappa (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) :
    ∃ (u : InfinitePlace E → HeightOneSpectrum (𝓞 E)) (κ : UA E n →* (InfinitePlace E → GL (Fin n) ℂ)),
      (∀ v, ((l : ℕ) : 𝓞 E) ∈ (u v).asIdeal ∧ ∀ x : 𝓞 E, x ∈ (u v).asIdeal → ‖ι.symm (v.embedding (x : E))‖ < 1) ∧
      (∀ g v, cLoc (u v) g = 1 → κ g v = 1) ∧ (∀ γ ∈ ratU E n, κ γ = cAll γ) ∧ (∀ x ∈ infU E n, κ x = 1) ∧
      ∀ (g : UA E n) (d : ℕ), DenomLe l d g → ∀ v i j,
        ‖ι.symm (((κ g v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ (l : ℝ) ^ d ∧
        ‖ι.symm ((((κ g v)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ (l : ℝ) ^ d := by
  have hex := fun v : InfinitePlace E =>
    GlobalTheory.LadicInf.exists_place E l (ι.symm.toRingHom.comp v.embedding)
  choose u j hl hj hjE using hex
  let f : InfinitePlace E → Af E →+* ℂ := fun v =>
    ι.toRingHom.comp ((j v).comp (pLoc E (u v)))
  let κ : UA E n →* (InfinitePlace E → GL (Fin n) ℂ) :=
    MonoidHom.pi fun v => (Matrix.GeneralLinearGroup.map ((f v).comp (pFin E))).comp (UA E n).subtype
  have hκ : ∀ (g : UA E n) (v : InfinitePlace E),
      κ g v = Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (j v)) (cLoc (u v) g) := by
    intro g v
    ext
    rfl
  refine ⟨u, κ, fun v => ⟨hl v, fun x hx => ?_⟩, fun g v hg => by rw [hκ, hg, map_one], ?_, ?_, ?_⟩
  · have h := congrArg (fun φ : E →+* Qbar l => φ (x : E)) (hjE v)
    simp only [RingHom.coe_comp, Function.comp_apply] at h
    have hv : Valued.v (algebraMap E ((u v).adicCompletion E) (x : E)) < 1 :=
      (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (u v) _).trans_lt
        ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) (u v) _).2 hx)
    have ht := ((hj v).tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one hv)
    have ht2 : Filter.Tendsto (fun m : ℕ => (j v (algebraMap E ((u v).adicCompletion E) (x : E))) ^ m) Filter.atTop (nhds 0) := by
      simpa [Function.comp_def, map_pow] using ht
    have := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ht2
    rw [h] at this
    exact this
  · rintro γ ⟨g₀, hg₀⟩
    funext v
    ext a b
    change (f v) (pFin E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) a b)) =
      coord v.embedding (pInf E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) a b))
    have hg₁ : (γ.1 : GL (Fin n) (Ad E)) = ratGL E n g₀ := hg₀.symm
    rw [hg₁]
    change (f v) (pFin E (algebraMap E (Ad E) ((g₀ : Matrix (Fin n) (Fin n) E) a b))) =
      coord v.embedding (pInf E (algebraMap E (Ad E) ((g₀ : Matrix (Fin n) (Fin n) E) a b)))
    rw [coord_algebraMap]
    have h := congrArg (fun φ : E →+* Qbar l => φ ((g₀ : Matrix (Fin n) (Fin n) E) a b)) (hjE v)
    simp only [RingHom.coe_comp, Function.comp_apply] at h
    change ι (j v (algebraMap E (u v |>.adicCompletion E) _)) = _
    rw [h]
    simp
  · intro x hx
    funext v
    have hx' : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
    have h2 : Matrix.GeneralLinearGroup.map ((f v).comp (pFin E)) x.1 =
        Matrix.GeneralLinearGroup.map (f v) (Matrix.GeneralLinearGroup.map (pFin E) x.1) := by ext; rfl
    change Matrix.GeneralLinearGroup.map ((f v).comp (pFin E)) x.1 = 1
    rw [h2, hx', map_one]
  · intro g d hd v a b
    obtain ⟨h1, h2⟩ := hd (u v) (hl v)
    constructor
    · rw [hκ g v]
      change ‖ι.symm (ι (j v (((cLoc (u v) g : GL (Fin n) ((u v).adicCompletion E)) :
        Matrix (Fin n) (Fin n) ((u v).adicCompletion E)) a b)))‖ ≤ _
      rw [RingEquiv.symm_apply_apply]
      exact norm_map_entry_le l (u v) (j v) (hl v) (hj v) d _ h1 a b
    · rw [hκ g v, ← map_inv]
      change ‖ι.symm (ι (j v ((((cLoc (u v) g)⁻¹ : GL (Fin n) ((u v).adicCompletion E)) :
        Matrix (Fin n) (Fin n) ((u v).adicCompletion E)) a b)))‖ ≤ _
      rw [RingEquiv.symm_apply_apply]
      exact norm_map_entry_le l (u v) (j v) (hl v) (hj v) d _ h2 a b

def IntL {E : Type} [Field E] [NumberField E] [IsCMField E] {a l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (lam : (E →+* ℂ) → DomWeight a) (f : UA E a →₀ ℂ) : Prop :=
  ∀ g ∈ f.support, g ∈ finU E a ∧ ∃ d : ℕ, DenomLe l d g ∧ ‖ι.symm (f g)‖ ≤ ((l : ℝ)⁻¹) ^ (a * d *
    ∑ᶠ (u : HeightOneSpectrum (𝓞 E)) (_ : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal ∧ cLoc u g ≠ 1), wtSizeOver ι lam u)

section Size

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

/- English proof (translation)
Establish `h1 : ∑ x ∈ I.disjSum I, sz (W.at (emb x)) ≤ ∑ τ ∈ X, sz (W.at τ)`. Rewrite using `[← Finset.sum_image (s := I.disjSum I) (g := emb) (f := fun τ => sz (W.at τ)) (fun x _ y _ h => emb_injective h)]`. Use `Finset.sum_le_sum_of_subset fun τ hτ => ?_` and prove the remaining obligations. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hτ`. Break down `x with v | v` into its components or cases.

Conclude with `(h v (by simpa using hx)).1`. Conclude with `(h v (by simpa using hx)).2`. Use `le_trans (le_of_eq ?_) h1` and prove the remaining obligations. Rewrite using `[Finset.sum_disjSum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Simplify using `only [emb]`. Rewrite using `[Wt.at_conjugate, sz_dual, Wt.at_embedding]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_le_of_mem (W : Wt E a) (I : Finset (InfinitePlace E)) (X : Finset (E →+* ℂ))
    (h : ∀ v ∈ I, v.embedding ∈ X ∧ ComplexEmbedding.conjugate v.embedding ∈ X) :
    ∑ v ∈ I, 2 * sz (W v) ≤ ∑ τ ∈ X, sz (W.at τ) := by
  classical
  have h1 : ∑ x ∈ I.disjSum I, sz (W.at (emb x)) ≤ ∑ τ ∈ X, sz (W.at τ) := by
    rw [← Finset.sum_image (s := I.disjSum I) (g := emb) (f := fun τ => sz (W.at τ))
      (fun x _ y _ h => emb_injective h)]
    refine Finset.sum_le_sum_of_subset fun τ hτ => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hτ
    rcases x with v | v
    · exact (h v (by simpa using hx)).1
    · exact (h v (by simpa using hx)).2
  refine le_trans (le_of_eq ?_) h1
  rw [Finset.sum_disjSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [emb]
  rw [Wt.at_conjugate, sz_dual, Wt.at_embedding]
  omega

/- English proof (translation)
The claim follows from `sum_le_of_mem W I Finset.univ fun _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩`.
-/
theorem sum_le_all (W : Wt E a) (I : Finset (InfinitePlace E)) : ∑ v ∈ I, 2 * sz (W v) ≤ wtSize W.at :=
  sum_le_of_mem W I Finset.univ fun _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩

open Classical in
/- English proof (translation)
Establish `hl0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Establish `hfin : {w : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ cLoc w g ≠ 1}.Finite` using `(Ideal.finite_factors hl0).subset fun w hw => Ideal.dvd_span_singleton.2 hw.1`. Establish `e` using `finsum_mem_eq_finite_toFinset_sum (fun w => wtSizeOver ι W.at w) hfin`.

Use `le_trans ?_ e.ge` and prove the remaining obligations. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (t := hfin.toFinset) (g := u) fun v hv => hfin.mem_toFinset.2 ⟨(hu v).1, (Finset.mem_filter.1 hv).2⟩]`. Use `Finset.sum_le_sum fun w _ => sum_le_of_mem W _ _ fun v hv => ?_` and prove the remaining obligations. Take `rfl : u v = w` from `(Finset.mem_filter.1 hv).2`. Use `⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl (hu v).2⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr fun x hx => ?_⟩⟩` and prove the remaining obligations.

Use `(hu v).2 x hx` as an intermediate fact. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]` and apply the resulting hypothesis.
-/
theorem sum_le_loc {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : Wt E a) (u : InfinitePlace E → HeightOneSpectrum (𝓞 E))
    (hu : ∀ v, ((l : ℕ) : 𝓞 E) ∈ (u v).asIdeal ∧ ∀ x : 𝓞 E, x ∈ (u v).asIdeal → ‖ι.symm (v.embedding (x : E))‖ < 1)
    (g : UA E a) : ∑ v ∈ Finset.univ.filter (fun v => cLoc (u v) g ≠ 1), 2 * sz (W v) ≤
      ∑ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ cLoc w g ≠ 1), wtSizeOver ι W.at w := by
  have hl0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ cLoc w g ≠ 1}.Finite :=
    (Ideal.finite_factors hl0).subset fun w hw => Ideal.dvd_span_singleton.2 hw.1
  have e := finsum_mem_eq_finite_toFinset_sum (fun w => wtSizeOver ι W.at w) hfin
  refine le_trans ?_ e.ge
  rw [← Finset.sum_fiberwise_of_maps_to (t := hfin.toFinset) (g := u) fun v hv =>
    hfin.mem_toFinset.2 ⟨(hu v).1, (Finset.mem_filter.1 hv).2⟩]
  refine Finset.sum_le_sum fun w _ => sum_le_of_mem W _ _ fun v hv => ?_
  obtain rfl : u v = w := (Finset.mem_filter.1 hv).2
  refine ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl (hu v).2⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr fun x hx => ?_⟩⟩
  have := (hu v).2 x hx
  rwa [ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]

end Size

/- English proof (translation)
Use function extensionality and compare the values at `v`. Establish `: cInf c = 1` using `hc`. Simplify using `[cAll, cEmb, this]`.
-/
theorem cAll_fin' {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {c : UA E n}
    (hc : c ∈ finU E n) : cAll c = 1 := by
  funext v
  have : cInf c = 1 := hc
  simp [cAll, cEmb, this]

/- English proof (translation)
Establish `hlp : l.Prime` using `Fact.out`. Take `⟨u, κ, hu, hκ1, hκr, hκi, hκd⟩` from `kappa E l ι a`. Set `ρ` to `Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W`. Set `M : UA E a → (InfinitePlace E → GL (Fin a) ℂ)` to `fun g => (cAll g)⁻¹ * κ g`. Set `b : UA E a → {x : W.Sp // CoefLe ι 1 x.1} → W.Sp` to `fun g x => ρ (M g) x.1`.

Establish `hl1 : (1 : ℝ) ≤ (l : ℝ)` using `by exact_mod_cast hlp.one_lt.le`. Establish `hpow : ∀ d : ℕ, (1 : ℝ) ≤ (l : ℝ) ^ d` using `fun d => one_le_pow₀ hl1`. Establish `hgrow : ∀ (c : UA E a) (d : ℕ), DenomLe l d c → ∀ x : W.Sp, CoefLe ι 1 x.1 → CoefLe ι (((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at)) (ρ (κ c) x).1` using `fun c d hc x hx => hR E l ι a W (κ c) _ (hpow d) (fun τ i j => hκd c d hc τ i j) x hx`. Establish `hgrowInv : ∀ (c : UA E a) (d : ℕ), DenomLe l d c → ∀ x : W.Sp, CoefLe ι 1 x.1 → CoefLe ι (((l : ℝ) ^ d) ^ (a * ∑ v ∈ Finset.univ.filter (fun v => cLoc (u v) c ≠ 1), 2 * sz (W v))) (ρ (κ c)⁻¹ x).1` using `fun c d hc x hx => rho_le ι W _ (κ c)⁻¹ _ (hpow d) (fun τ i j => by`. Establish `h` using `hκd c d hc τ i j`.

Simplify using `only [Pi.inv_apply, inv_inv]`. Use `split_ifs with hτ`. Conclude with `⟨h.2, h.1⟩`. Establish `h1 : κ c τ = 1` using `hκ1 c τ (by simpa using hτ)`. Rewrite using `[h1, inv_one, Units.val_one, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp) x hx`. Establish `hval : ∀ f : algForms W, ∀ γ ∈ ratU E a, ∀ s x, x ∈ infU E a → ∀ c : finU E a, (∀ v g, f.1 v (g * (c : UA E a)) = f.1 v g) → ∀ v, f.1 (ρ (M (γ * s * x * c)) v) (γ * s * x * c) = f.1 (ρ (M s) (ρ (κ (c : UA E a)) v)) s`. Introduce `f γ hγ s x hx c hf v`. Establish `hM : cAll x * M (γ * s * x * c) = M s * κ (c : UA E a)`. Simplify using `only [M, map_mul, hκr γ hγ, hκi x hx, cAll_fin' c.2, mul_one]`.

Use `group`. Establish `hA : ∀ v, f.1 v (γ * s * x * c) = f.1 v (s * c * x)`. Introduce `v`. Rewrite using `[mul_assoc γ s, mul_assoc γ, (f.2.1 v).left γ hγ, mul_assoc s x, ← fin_mul_inf c.2 hx, ← mul_assoc]`. Establish `hB : ∀ v, f.1 v (s * c * x) = f.1 (W.rep ⟨x, hx⟩ v) (s * c)`.

Introduce `v`. Rewrite using `[f.2.2 ⟨x, hx⟩ v]`. Both sides reduce to the same expression. Establish `e3 : W.rep ⟨x, hx⟩ (ρ (M (γ * s * x * c)) v) = ρ (M s) (ρ (κ (c : UA E a)) v)`. Express the relevant statement in the definitionally equal form `ρ (cAll x) (ρ (M _) v) = _`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, hM, map_mul, Module.End.mul_apply]`. Rewrite using `[hA, hB, hf, e3]`. Use `⟨{x : W.Sp // CoefLe ι 1 x.1}, b, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f`. Take `⟨C, hC, hfC⟩` from `hE E a W f`.

Take `⟨d, hd⟩` from `hD E l hlp a C hC.compact`. Set `C₃ : Subgroup (finU E a)` to `C.subgroupOf (finU E a)`. Establish `hC₃o : IsOpen (C₃ : Set (finU E a))`. Take `⟨N, hNo, hN1, hNC⟩` from `hC.isOpen`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hNo.preimage continuous_subtype_val).mem_nhds hN1) ?_)` and prove the remaining obligations.

Introduce `x hx`. Conclude with `Subgroup.mem_subgroupOf.2 (hNC ⟨hx, x.2⟩)`. Take `⟨S, hS⟩` from `GlobalTheory.DefU.ClassFin.classSet_finite E a C₃ hC₃o`. Set `φ : UA E a → (W.Sp →ₗ[ℂ] ℂ)` to `fun s => (LinearMap.proj s) ∘ₗ f.1 ∘ₗ (ρ (M s))`. Establish `hφ : ∀ s, ∃ m : ℝ, 0 ≤ m ∧ ∀ (R : ℝ) (x : W.Sp), CoefLe ι R x.1 → ‖ι.symm (φ s x)‖ ≤ m * R` using `fun s => (hL l ι _ (Formalism.L2.DIV.VV ℂ W)).1 (φ s)`.

Use `choose m hm0 hm using hφ`. Use `⟨(∑ s ∈ S, m s) * ((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at), fun g i => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, s, hs, y, hy, c, hc, rfl⟩` from `hS g`. Establish `hcC : (c : UA E a) ∈ C` using `Subgroup.mem_subgroupOf.1 hc`. Establish `e` using `hval f γ hγ s y hy c (fun v g => hfC _ hcC v g) i.1`.

Establish `hb : f.1 (b (γ * s * y * c) i) (γ * s * y * c) = φ s (ρ (κ (c : UA E a)) i.1)` using `e`. Rewrite using `[hb]`. Use `(hm s _ _ (hgrow _ d (hd _ hcC) i.1 i.2)).trans ?_` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun q _ => hm0 q) hs) (by positivity)`. Introduce `f h0`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Use function extensionality and compare the values at `g`. Take `⟨c, hc0, hc⟩` from `(hL l ι _ (Formalism.L2.DIV.VV ℂ W)).2 (ρ (M g)⁻¹ v)`.

Establish `h1` using `h0 g ⟨c • ρ (M g)⁻¹ v, hc⟩`. Establish `h2 : b g ⟨c • ρ (M g)⁻¹ v, hc⟩ = c • v`. Express the relevant statement in the definitionally equal form `ρ (M g) (c • ρ (M g)⁻¹ v) = c • v`. Rewrite using `[map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Rewrite `h1` using `[h2, map_smul, Pi.smul_apply, smul_eq_mul]`.

Conclude with `(mul_eq_zero.1 h1).resolve_left hc0`. Introduce `F R hF j g i`. Establish `hR0 : 0 ≤ R` using `(norm_nonneg _).trans (hF g i)`. Establish `e : opOf (RU E a) (t j) (F (b g i)) g = ∑ h ∈ (t j).support, t j h * F (b g i) (g * h)`. Simplify using `only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, RU_apply, smul_eq_mul]`.

Rewrite using `[e, map_sum]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR0 fun h hh => ?_` and prove the remaining obligations. Establish `hinv : ((l : ℝ)⁻¹) ≤ 1` using `inv_le_one_of_one_le₀ hl1`. Choose the witnesses or unpack the hypotheses as in `⟨hfin, d, hd, hn⟩ : h ∈ finU E a ∧ ∃ d : ℕ, DenomLe l d h ∧ ‖ι.symm (t j h)‖ ≤ ((l : ℝ)⁻¹) ^ (a * d * ∑ v ∈ Finset.univ.filter (fun v => cLoc (u v) h ≠ 1), 2 * sz (W v)) := by`. Break down `ht j with ht | ht` into its components or cases.

Take `⟨hfin, d, hd, hn⟩` from `ht h hh`. Conclude with `⟨hfin, d, hd, hn.trans (pow_le_pow_of_le_one (by positivity) hinv (Nat.mul_le_mul_left _ (sum_le_all W _)))⟩`. Take `⟨hfin, d, hd, hn⟩` from `ht h hh`. Conclude with `⟨hfin, d, hd, hn.trans (pow_le_pow_of_le_one (by positivity) hinv (Nat.mul_le_mul_left _ (sum_le_loc ι W u hu h)))⟩`. Establish `hyc` using `hgrowInv h d hd i.1 i.2`.

Generalize the expression as in `(∑ v ∈ Finset.univ.filter (fun v => cLoc (u v) h ≠ 1), 2 * sz (W v)) = s at hn hyc`. Establish `hMh : M g = M (g * h) * (κ h)⁻¹`. Simplify using `only [M, map_mul, cAll_fin' hfin, mul_one]`. Use `group`. Use `set y : W.Sp := ρ (κ h)⁻¹ i.1 with hy`.

Establish `hx : CoefLe ι 1 ((t j h • y : W.Sp) : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a)`. Introduce `q`. Establish `hq` using `hyc q`. Establish `e1 : MvPolynomial.coeff q ((t j h • y : W.Sp) : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) = t j h * MvPolynomial.coeff q (y : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a)`. Simplify using `[MvPolynomial.coeff_smul]`.

Rewrite using `[e1, map_mul, norm_mul]`. Establish `hlpos : (0 : ℝ) < (l : ℝ)` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_mul, inv_pow, show d * (a * s) = a * d * s by ring]`. Conclude with `inv_mul_cancel₀ (by positivity)`.

Establish `hb : t j h * F (b g i) (g * h) = F (b (g * h) ⟨t j h • y, hx⟩) (g * h)`. Establish `: b g i = ρ (M (g * h)) y`. Express the relevant statement in the definitionally equal form `ρ (M g) i.1 = _`. Rewrite using `[hMh, map_mul, Module.End.mul_apply]`. Express the relevant statement in the definitionally equal form `_ = F (ρ (M (g * h)) (t j h • y)) (g * h)`.

Rewrite using `[this, map_smul, map_smul, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hb]`. Conclude with `hF _ _`.
-/
theorem frame (hD : DenomBdd) (hR : RhoBound) (hL : LatFacts) (hE : LevelEx) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (W : Wt E a) {J : Type} (t : J → (UA E a →₀ ℂ))
    (ht : ∀ j, IntW ι W.at (t j) ∨ IntL ι W.at (t j)) : FramedX ι W t := by
  classical
  have hlp : l.Prime := Fact.out
  obtain ⟨u, κ, hu, hκ1, hκr, hκi, hκd⟩ := kappa E l ι a
  let ρ := Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W
  let M : UA E a → (InfinitePlace E → GL (Fin a) ℂ) := fun g => (cAll g)⁻¹ * κ g
  let b : UA E a → {x : W.Sp // CoefLe ι 1 x.1} → W.Sp := fun g x => ρ (M g) x.1
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hlp.one_lt.le
  have hpow : ∀ d : ℕ, (1 : ℝ) ≤ (l : ℝ) ^ d := fun d => one_le_pow₀ hl1
  have hgrow : ∀ (c : UA E a) (d : ℕ), DenomLe l d c → ∀ x : W.Sp, CoefLe ι 1 x.1 →
      CoefLe ι (((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at)) (ρ (κ c) x).1 := fun c d hc x hx =>
    hR E l ι a W (κ c) _ (hpow d) (fun τ i j => hκd c d hc τ i j) x hx
  have hgrowInv : ∀ (c : UA E a) (d : ℕ), DenomLe l d c → ∀ x : W.Sp, CoefLe ι 1 x.1 →
      CoefLe ι (((l : ℝ) ^ d) ^ (a * ∑ v ∈ Finset.univ.filter (fun v => cLoc (u v) c ≠ 1), 2 * sz (W v))) (ρ (κ c)⁻¹ x).1 :=
    fun c d hc x hx => rho_le ι W _ (κ c)⁻¹ _ (hpow d) (fun τ i j => by
      have h := hκd c d hc τ i j
      simp only [Pi.inv_apply, inv_inv]
      split_ifs with hτ
      · exact ⟨h.2, h.1⟩
      · have h1 : κ c τ = 1 := hκ1 c τ (by simpa using hτ)
        rw [h1, inv_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> simp) x hx
  have hval : ∀ f : algForms W, ∀ γ ∈ ratU E a, ∀ s x, x ∈ infU E a → ∀ c : finU E a,
      (∀ v g, f.1 v (g * (c : UA E a)) = f.1 v g) → ∀ v,
      f.1 (ρ (M (γ * s * x * c)) v) (γ * s * x * c) = f.1 (ρ (M s) (ρ (κ (c : UA E a)) v)) s := by
    intro f γ hγ s x hx c hf v
    have hM : cAll x * M (γ * s * x * c) = M s * κ (c : UA E a) := by
      simp only [M, map_mul, hκr γ hγ, hκi x hx, cAll_fin' c.2, mul_one]
      group
    have hA : ∀ v, f.1 v (γ * s * x * c) = f.1 v (s * c * x) := by
      intro v
      rw [mul_assoc γ s, mul_assoc γ, (f.2.1 v).left γ hγ, mul_assoc s x, ← fin_mul_inf c.2 hx, ← mul_assoc]
    have hB : ∀ v, f.1 v (s * c * x) = f.1 (W.rep ⟨x, hx⟩ v) (s * c) := by
      intro v
      rw [f.2.2 ⟨x, hx⟩ v]
      rfl
    have e3 : W.rep ⟨x, hx⟩ (ρ (M (γ * s * x * c)) v) = ρ (M s) (ρ (κ (c : UA E a)) v) := by
      change ρ (cAll x) (ρ (M _) v) = _
      rw [← Module.End.mul_apply, ← map_mul, hM, map_mul, Module.End.mul_apply]
    rw [hA, hB, hf, e3]
  refine ⟨{x : W.Sp // CoefLe ι 1 x.1}, b, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨C, hC, hfC⟩ := hE E a W f
    obtain ⟨d, hd⟩ := hD E l hlp a C hC.compact
    let C₃ : Subgroup (finU E a) := C.subgroupOf (finU E a)
    have hC₃o : IsOpen (C₃ : Set (finU E a)) := by
      obtain ⟨N, hNo, hN1, hNC⟩ := hC.isOpen
      refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
        (Filter.mem_of_superset ((hNo.preimage continuous_subtype_val).mem_nhds hN1) ?_)
      intro x hx
      exact Subgroup.mem_subgroupOf.2 (hNC ⟨hx, x.2⟩)
    obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E a C₃ hC₃o
    let φ : UA E a → (W.Sp →ₗ[ℂ] ℂ) := fun s => (LinearMap.proj s) ∘ₗ f.1 ∘ₗ (ρ (M s))
    have hφ : ∀ s, ∃ m : ℝ, 0 ≤ m ∧ ∀ (R : ℝ) (x : W.Sp), CoefLe ι R x.1 → ‖ι.symm (φ s x)‖ ≤ m * R :=
      fun s => (hL l ι _ (Formalism.L2.DIV.VV ℂ W)).1 (φ s)
    choose m hm0 hm using hφ
    refine ⟨(∑ s ∈ S, m s) * ((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at), fun g i => ?_⟩
    obtain ⟨γ, hγ, s, hs, y, hy, c, hc, rfl⟩ := hS g
    have hcC : (c : UA E a) ∈ C := Subgroup.mem_subgroupOf.1 hc
    have e := hval f γ hγ s y hy c (fun v g => hfC _ hcC v g) i.1
    have hb : f.1 (b (γ * s * y * c) i) (γ * s * y * c) = φ s (ρ (κ (c : UA E a)) i.1) := e
    rw [hb]
    refine (hm s _ _ (hgrow _ d (hd _ hcC) i.1 i.2)).trans ?_
    exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun q _ => hm0 q) hs) (by positivity)
  · intro f h0
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    funext g
    obtain ⟨c, hc0, hc⟩ := (hL l ι _ (Formalism.L2.DIV.VV ℂ W)).2 (ρ (M g)⁻¹ v)
    have h1 := h0 g ⟨c • ρ (M g)⁻¹ v, hc⟩
    have h2 : b g ⟨c • ρ (M g)⁻¹ v, hc⟩ = c • v := by
      change ρ (M g) (c • ρ (M g)⁻¹ v) = c • v
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [h2, map_smul, Pi.smul_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hc0
  · intro F R hF j g i
    have hR0 : 0 ≤ R := (norm_nonneg _).trans (hF g i)
    have e : opOf (RU E a) (t j) (F (b g i)) g = ∑ h ∈ (t j).support, t j h * F (b g i) (g * h) := by
      simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, RU_apply, smul_eq_mul]
    rw [e, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR0 fun h hh => ?_
    have hinv : ((l : ℝ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ hl1
    obtain ⟨hfin, d, hd, hn⟩ : h ∈ finU E a ∧ ∃ d : ℕ, DenomLe l d h ∧ ‖ι.symm (t j h)‖ ≤
        ((l : ℝ)⁻¹) ^ (a * d * ∑ v ∈ Finset.univ.filter (fun v => cLoc (u v) h ≠ 1), 2 * sz (W v)) := by
      rcases ht j with ht | ht
      · obtain ⟨hfin, d, hd, hn⟩ := ht h hh
        exact ⟨hfin, d, hd, hn.trans (pow_le_pow_of_le_one (by positivity) hinv (Nat.mul_le_mul_left _ (sum_le_all W _)))⟩
      · obtain ⟨hfin, d, hd, hn⟩ := ht h hh
        exact ⟨hfin, d, hd, hn.trans (pow_le_pow_of_le_one (by positivity) hinv (Nat.mul_le_mul_left _ (sum_le_loc ι W u hu h)))⟩
    have hyc := hgrowInv h d hd i.1 i.2
    generalize (∑ v ∈ Finset.univ.filter (fun v => cLoc (u v) h ≠ 1), 2 * sz (W v)) = s at hn hyc
    have hMh : M g = M (g * h) * (κ h)⁻¹ := by
      simp only [M, map_mul, cAll_fin' hfin, mul_one]
      group
    set y : W.Sp := ρ (κ h)⁻¹ i.1 with hy
    have hx : CoefLe ι 1 ((t j h • y : W.Sp) : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) := by
      intro q
      have hq := hyc q
      have e1 : MvPolynomial.coeff q ((t j h • y : W.Sp) : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) =
          t j h * MvPolynomial.coeff q (y : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) := by
        simp [MvPolynomial.coeff_smul]
      rw [e1, map_mul, norm_mul]
      have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
      calc _ ≤ ((l : ℝ)⁻¹) ^ (a * d * s) * ((l : ℝ) ^ d) ^ (a * s) :=
            mul_le_mul hn hq (norm_nonneg _) (by positivity)
        _ = 1 := by
            rw [← pow_mul, inv_pow, show d * (a * s) = a * d * s by ring]
            exact inv_mul_cancel₀ (by positivity)
    have hb : t j h * F (b g i) (g * h) = F (b (g * h) ⟨t j h • y, hx⟩) (g * h) := by
      have : b g i = ρ (M (g * h)) y := by
        change ρ (M g) i.1 = _
        rw [hMh, map_mul, Module.End.mul_apply]
      change _ = F (ρ (M (g * h)) (t j h • y)) (g * h)
      rw [this, map_smul, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [hb]
    exact hF _ _

end UpperTheory.Gal.Gen.Loc

namespace UpperTheory.Gal.Gen

end UpperTheory.Gal.Gen

end
