import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicCharacterUnitary
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

/- English proof (translation)
Establish `hvl : Valued.v ((l : ℕ) : u.adicCompletion E) < 1`. Establish `h1 : u.valuation E (((l : ℕ) : 𝓞 E) : E) < 1` using `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) u _).2 hl`. Establish `h2 : (((l : ℕ) : u.adicCompletion E)) = algebraMap E (u.adicCompletion E) (((l : ℕ) : 𝓞 E) : E)` using `by simp`. Rewrite using `[h2]`. Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _).trans_lt h1`.

Establish `hlnorm : ‖j ((l : ℕ) : u.adicCompletion E)‖ = (l : ℝ)⁻¹`. Establish `h0 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[map_natCast, h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l]), Padic.norm_p]`. Establish `hlt : ∀ k : ℕ, ‖j ((l : ℕ) : u.adicCompletion E)‖ * ‖j y‖ ^ k < 1`. Introduce `k`.

Establish `hyv : Valued.v y ≤ 1` using `hy`. Establish `hv : Valued.v (((l : ℕ) : u.adicCompletion E) * y ^ k) < 1`. Rewrite using `[map_mul, map_pow]`. Conclude with `mul_lt_one_of_lt_of_le hvl (pow_le_one' hyv k)`. Establish `ht` using `Valued.tendsto_zero_pow_of_v_lt_one hv`.

Establish `ht2 : Filter.Tendsto (fun m : ℕ => (j (((l : ℕ) : u.adicCompletion E) * y ^ k)) ^ m) Filter.atTop (nhds 0)`. Use `(hj.tendsto 0).comp ht` as an intermediate fact. Simplify `this` using `[Function.comp_def, map_pow]`. Use `tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ht2` as an intermediate fact. Simplify `this` using `[map_mul, map_pow, norm_mul, norm_pow]`.

Assume the negation of the conclusion as `hcon`. Establish `hgt : 1 < ‖j y‖` using `not_le.1 hcon`. Establish `hlpos : 0 < ‖j ((l : ℕ) : u.adicCompletion E)‖`. Rewrite using `[hlnorm]`. Conclude with `inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)`.

Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (‖j ((l : ℕ) : u.adicCompletion E)‖⁻¹) hgt`. Use `hlt k` as an intermediate fact. Establish `h3 : 1 < ‖j ((l : ℕ) : u.adicCompletion E)‖ * ‖j y‖ ^ k`. Rewrite `hk` using `[inv_lt_iff_one_lt_mul₀ hlpos]`. Conclude with `hk.trans_eq (mul_comm _ _)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem norm_map_integer_le_one {E : Type} [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
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
private theorem norm_map_entry_le {E : Type} [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] {n : ℕ}
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
Introduce `E _ _ _ l _ ι n`. Establish `hex` using `fun v : InfinitePlace E => GlobalTheory.LadicInf.exists_place E l (ι.symm.toRingHom.comp v.embedding)`. Use `choose u j hl hj hjE using hex`. Set `f : InfinitePlace E → Af E →+* ℂ` to `fun v => ι.toRingHom.comp ((j v).comp (pLoc E (u v)))`. Set `κ : UA E n →* (InfinitePlace E → GL (Fin n) ℂ)` to `MonoidHom.pi fun v => (Matrix.GeneralLinearGroup.map ((f v).comp (pFin E))).comp (UA E n).subtype`.

Establish `hκ : ∀ (g : UA E n) (v : InfinitePlace E), κ g v = Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (j v)) (cLoc (u v) g)`. Introduce `g v`. Use `ext`. Both sides reduce to the same expression. Use `⟨κ, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `γ ⟨g₀, hg₀⟩`. Use function extensionality and compare the values at `v`. Use extensionality with `a b`. Express the relevant statement in the definitionally equal form `(f v) (pFin E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) a b)) = coord v.embedding (pInf E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) a b))`. Establish `hg₁ : (γ.1 : GL (Fin n) (Ad E)) = ratGL E n g₀` using `hg₀.symm`.

Rewrite using `[hg₁]`. Express the relevant statement in the definitionally equal form `(f v) (pFin E (algebraMap E (Ad E) ((g₀ : Matrix (Fin n) (Fin n) E) a b))) = coord v.embedding (pInf E (algebraMap E (Ad E) ((g₀ : Matrix (Fin n) (Fin n) E) a b)))`. Rewrite using `[coord_algebraMap]`. Establish `h` using `congrArg (fun φ : E →+* Qbar l => φ ((g₀ : Matrix (Fin n) (Fin n) E) a b)) (hjE v)`. Simplify using `only [RingHom.coe_comp, Function.comp_apply] at h`.

Express the relevant statement in the definitionally equal form `ι (j v (algebraMap E (u v |>.adicCompletion E) _)) = _`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Introduce `x hx`. Use function extensionality and compare the values at `v`.

Establish `hx' : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1` using `hx`. Establish `h2 : Matrix.GeneralLinearGroup.map ((f v).comp (pFin E)) x.1 = Matrix.GeneralLinearGroup.map (f v) (Matrix.GeneralLinearGroup.map (pFin E) x.1)` using `by ext; rfl`. Express the relevant statement in the definitionally equal form `Matrix.GeneralLinearGroup.map ((f v).comp (pFin E)) x.1 = 1`. Rewrite using `[h2, hx', map_one]`. Introduce `g d hd v a b`.

Take `⟨h1, h2⟩` from `hd (u v) (hl v)`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hκ g v]`. Express the relevant statement in the definitionally equal form `‖ι.symm (ι (j v (((cLoc (u v) g : GL (Fin n) ((u v).adicCompletion E)) : Matrix (Fin n) (Fin n) ((u v).adicCompletion E)) a b)))‖ ≤ _`. Rewrite using `[RingEquiv.symm_apply_apply]`.

Conclude with `norm_map_entry_le l (u v) (j v) (hl v) (hj v) d _ h1 a b`. Rewrite using `[hκ g v, ← map_inv]`. Express the relevant statement in the definitionally equal form `‖ι.symm (ι (j v ((((cLoc (u v) g)⁻¹ : GL (Fin n) ((u v).adicCompletion E)) : Matrix (Fin n) (Fin n) ((u v).adicCompletion E)) a b)))‖ ≤ _`. Rewrite using `[RingEquiv.symm_apply_apply]`. Conclude with `norm_map_entry_le l (u v) (j v) (hl v) (hj v) d _ h2 a b`.
-/
theorem UpperTheory.Gal.Gen.kappa_pf :
    UpperTheory.Gal.Gen.Kappa := by
  intro E _ _ _ l _ ι n
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
  refine ⟨κ, ?_, ?_, ?_⟩
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
