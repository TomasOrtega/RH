import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.KTFiniteDimensional

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

/- English proof (translation)
Establish `h : ∃ a : Ω, f = a • f` using `⟨1, (one_smul _ _).symm⟩`. Rewrite using `[ratio, dif_pos h]`. Establish `hc` using `h.choose_spec`. Establish `h0 : (h.choose - 1) • f = 0` using `by rw [sub_smul, ← hc, one_smul, sub_self]`. Break down `smul_eq_zero.mp h0 with h1 | h1` into its components or cases.

Conclude with `sub_eq_zero.mp h1`. Conclude with `absurd h1 hf`.
-/
theorem ratio_self {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f : V} (hf : f ≠ 0) :
    ratio (Ω := Ω) f f = 1 := by
  have h : ∃ a : Ω, f = a • f := ⟨1, (one_smul _ _).symm⟩
  rw [ratio, dif_pos h]
  have hc := h.choose_spec
  have h0 : (h.choose - 1) • f = 0 := by rw [sub_smul, ← hc, one_smul, sub_self]
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hf

/- English proof (translation)
Use `show Fin.insertNth (α := fun _ => β) i x p i = x`. Conclude with `Fin.insertNth_apply_same _ _ _`.
-/
theorem sac_self {β : Type*} {n : ℕ} (i : Fin (n + 1)) (x : β) (p : Fin n → β) :
    Fin.succAboveCases (α := fun _ => β) i x p i = x := by
  show Fin.insertNth (α := fun _ => β) i x p i = x
  exact Fin.insertNth_apply_same _ _ _

/- English proof (translation)
Use `show Fin.insertNth (α := fun _ => β) i x p (i.succAbove k) = p k`. Conclude with `Fin.insertNth_apply_succAbove _ _ _ _`.
-/
theorem sac_succAbove {β : Type*} {n : ℕ} (i : Fin (n + 1)) (x : β) (p : Fin n → β) (k : Fin n) :
    Fin.succAboveCases (α := fun _ => β) i x p (i.succAbove k) = p k := by
  show Fin.insertNth (α := fun _ => β) i x p (i.succAbove k) = p k
  exact Fin.insertNth_apply_succAbove _ _ _ _

noncomputable def tauPev {K : Type} [Field K] {D N : ℕ} (sg : K →+* ℂ) (pt : TVar D N → ℂ)
    (hpt : ∀ q : MvPolynomial (TVar D N) K, q ≠ 0 → eval₂ sg pt q ≠ 0) : KTf K D N →+* ℂ :=
  IsFractionRing.lift (A := KTp K D N) (g := eval₂Hom sg pt)
    ((injective_iff_map_eq_zero _).2 fun q hq => by_contra fun h0 => hpt q h0 hq)

/- English proof (translation)
Rewrite using `[tauPev, IsFractionRing.lift_algebraMap]`. Both sides reduce to the same expression.
-/
theorem tauPev_apply {K : Type} [Field K] {D N : ℕ} (sg : K →+* ℂ) (pt : TVar D N → ℂ)
    (hpt : ∀ q : MvPolynomial (TVar D N) K, q ≠ 0 → eval₂ sg pt q ≠ 0) (q : KTp K D N) :
    tauPev sg pt hpt (algebraMap (KTp K D N) (KTf K D N) q) = eval₂ sg pt q := by
  rw [tauPev, IsFractionRing.lift_algebraMap]
  rfl

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def pImg (c : ι) (p : TVar d.D d.N) : MvPolynomial (SVar d.D d.N) (Ω c) :=
  Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c)
    (if p.1 = 0 then X (Sum.inl ())
      else -∑ k, X (Sum.inr (p.1, k)) * C (d.x c k))
    (fun k => X (Sum.inr (p.1, k))) p.2

noncomputable def sHp (c : ι) : MvPolynomial (TVar d.D d.N) K →ₐ[K] MvPolynomial (SVar d.D d.N) (Ω c) :=
  aeval (d.pImg c)

/- English proof (translation)
Establish `e : d.sH c = (IsScalarTower.toAlgHom K (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)).comp (d.sHp c)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`. Rewrite using `[AlgHom.comp_apply, sHp, MvPolynomial.aeval_X, IsScalarTower.coe_toAlgHom', sH, sHom, MvPolynomial.aeval_X]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem sH_eq (c : ι) (q : MvPolynomial (TVar d.D d.N) K) :
    d.sH c q = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (d.sHp c q) := by
  have e : d.sH c = (IsScalarTower.toAlgHom K (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N)).comp (d.sHp c) := by
    apply MvPolynomial.algHom_ext
    intro p
    rw [AlgHom.comp_apply, sHp, MvPolynomial.aeval_X, IsScalarTower.coe_toAlgHom', sH, sHom,
      MvPolynomial.aeval_X]
    rfl
  rw [e]
  rfl

/- English proof (translation)
The claim follows from `(IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) a).symm`.
-/
theorem algC (c : ι) (a : Ω c) :
    algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (C a) =
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) a := (IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c))
    (OmS (Ω c) d.D d.N) a).symm

/- English proof (translation)
Establish `hr : ∀ j, algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω` using `Ω c) (d.w j c) (d.w (d.jc c) c)) = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (C (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) := fun j => (d.algC c _).symm`. Establish `hx : ∀ k, ratio (Ω` using `Ω c) (d.w ((d.jc c).succAbove k) c) (d.w (d.jc c) c) = d.x c k := fun k => rfl`. Repeatedly rewrite using `[hr, d.sH_eq, ← map_mul, ← map_sum]`. Rewrite using `[Fin.sum_univ_succAbove _ (d.jc c)]`. Simplify using `only [sHp, MvPolynomial.aeval_X, pImg, sac_self, sac_succAbove, ratio_self (hd.w_base c), Fin.succ_ne_zero, if_false, hx, MvPolynomial.C_1, mul_one, neg_add_cancel, map_zero]`.
-/
theorem sH_rel (hd : d.AxH 𝒜) (c : ι) (i : Fin d.D) :
    ∑ j, d.sH c (X (i.succ, j)) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
      (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) = 0 := by
  have hr : ∀ j, algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) =
      algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
        (C (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) := fun j => (d.algC c _).symm
  have hx : ∀ k, ratio (Ω := Ω c) (d.w ((d.jc c).succAbove k) c) (d.w (d.jc c) c) = d.x c k :=
    fun k => rfl
  simp_rw [hr, d.sH_eq, ← map_mul, ← map_sum]
  rw [Fin.sum_univ_succAbove _ (d.jc c)]
  simp only [sHp, MvPolynomial.aeval_X, pImg, sac_self, sac_succAbove, ratio_self (hd.w_base c),
    Fin.succ_ne_zero, if_false, hx, MvPolynomial.C_1, mul_one, neg_add_cancel, map_zero]

noncomputable def evP (c : ι) (P : Ω c →+* ℂ) (pt : TVar d.D d.N → ℂ) :
    MvPolynomial (SVar d.D d.N) (Ω c) →+* ℂ :=
  eval₂Hom P (Sum.elim (fun _ => pt (0, d.jc c)) (fun ik => pt (ik.1, (d.jc c).succAbove ik.2)))

/- English proof (translation)
Establish `hP' : P.comp (algebraMap K (Ω c)) = sg` using `hP`. Establish `hx : ∀ k, ratio (Ω` using `Ω c) (d.w ((d.jc c).succAbove k) c) (d.w (d.jc c) c) = d.x c k := fun k => rfl`. Establish `key : (d.evP c P pt).comp (d.sHp c).toRingHom = eval₂Hom sg pt`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`.

Rewrite using `[RingHom.comp_apply, eval₂Hom_C]`. Establish `h1 : (d.sHp c).toRingHom (C a) = C (algebraMap K (Ω c) a)` using `by show d.sHp c (algebraMap K _ a) = _`. Rewrite using `[AlgHom.commutes, MvPolynomial.algebraMap_apply]`. Rewrite using `[h1, evP, eval₂Hom_C]`. Conclude with `RingHom.congr_fun hP' a`.

Introduce and unpack `⟨i, j⟩`. Rewrite using `[RingHom.comp_apply, eval₂Hom_X']`. Use `show d.evP c P pt (d.sHp c (X (i, j))) = pt (i, j)`. Rewrite using `[sHp, aeval_X, pImg]`. Simplify using `only`.

Break down `Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩` into its components or cases. Rewrite using `[sac_self]`. Consider the cases of `i using Fin.cases with`. Consider the case `zero => simp [evP]`. Consider the case `succ i'`.

Rewrite using `[if_neg (Fin.succ_ne_zero i')]`. Establish `h1` using `heq i'`. Rewrite `h1` using `[Fin.sum_univ_succAbove _ (d.jc c), ratio_self (hd.w_base c), map_one, mul_one]`. Simplify using `only [hx] at h1`. Simplify using `only [evP, map_neg, map_sum, map_mul, eval₂Hom_X', eval₂Hom_C, Sum.elim_inr]`.

Take the linear combination `-h1`. Rewrite using `[sac_succAbove]`. Simplify using `[evP]`. Conclude with `RingHom.congr_fun key q`.
-/
theorem evP_sHp (c : ι) (sg : K →+* ℂ) (pt : TVar d.D d.N → ℂ) (hd : d.AxH 𝒜) (P : Ω c →+* ℂ)
    (hP : P ∈ PT (Ω := Ω c) sg)
    (heq : ∀ i : Fin d.D, ∑ j, pt (i.succ, j) * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) = 0)
    (q : MvPolynomial (TVar d.D d.N) K) : d.evP c P pt (d.sHp c q) = eval₂ sg pt q := by
  have hP' : P.comp (algebraMap K (Ω c)) = sg := hP
  have hx : ∀ k, ratio (Ω := Ω c) (d.w ((d.jc c).succAbove k) c) (d.w (d.jc c) c) = d.x c k :=
    fun k => rfl
  have key : (d.evP c P pt).comp (d.sHp c).toRingHom = eval₂Hom sg pt := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, eval₂Hom_C]
      have h1 : (d.sHp c).toRingHom (C a) = C (algebraMap K (Ω c) a) := by
        show d.sHp c (algebraMap K _ a) = _
        rw [AlgHom.commutes, MvPolynomial.algebraMap_apply]
      rw [h1, evP, eval₂Hom_C]
      exact RingHom.congr_fun hP' a
    · rintro ⟨i, j⟩
      rw [RingHom.comp_apply, eval₂Hom_X']
      show d.evP c P pt (d.sHp c (X (i, j))) = pt (i, j)
      rw [sHp, aeval_X, pImg]
      dsimp only
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · rw [sac_self]
        cases i using Fin.cases with
        | zero => simp [evP]
        | succ i' =>
          rw [if_neg (Fin.succ_ne_zero i')]
          have h1 := heq i'
          rw [Fin.sum_univ_succAbove _ (d.jc c), ratio_self (hd.w_base c), map_one, mul_one] at h1
          simp only [hx] at h1
          simp only [evP, map_neg, map_sum, map_mul, eval₂Hom_X', eval₂Hom_C, Sum.elim_inr]
          linear_combination -h1
      · rw [sac_succAbove]
        simp [evP]
  exact RingHom.congr_fun key q

section emb

variable (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (pt : TVar d.D d.N → ℂ)
  (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 → eval₂ sg pt q ≠ 0)

/- English proof (translation)
Rewrite using `[KTtoS, IsFractionRing.lift_algebraMap]`. Both sides reduce to the same expression.
-/
theorem KTtoS_alg (q : KTp K d.D d.N) :
    d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q) = d.sH c q := by
  rw [KTtoS, IsFractionRing.lift_algebraMap]
  rfl

include hpt in
/- English proof (translation)
Rewrite using `[← d.KTtoS_alg h c q, ← RingHom.comp_apply, hσ, tauPev_apply]`.
-/
theorem emb_sH (σ : OmS (Ω c) d.D d.N →+* ℂ) (hσ : σ.comp (d.KTtoS h c) = tauPev sg pt hpt)
    (q : MvPolynomial (TVar d.D d.N) K) : σ (d.sH c q) = eval₂ sg pt q := by
  rw [← d.KTtoS_alg h c q, ← RingHom.comp_apply, hσ, tauPev_apply]

include hd in
/- English proof (translation)
Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Use `show (σ.comp (algebraMap (Ω c) (OmS (Ω c) d.D d.N))).comp (algebraMap K (Ω c)) = sg`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Establish `h1` using `d.emb_sH h c sg pt hpt σ hσ (C a)`. Establish `h2` using `(d.sH c).commutes a`.

Rewrite `h2` using `[MvPolynomial.algebraMap_eq]`. Rewrite `h1` using `[h2, eval₂_C]`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]`. Conclude with `h1`. Establish `h2` using `congrArg σ (d.sH_rel hd c i)`.

Rewrite `h2` using `[map_sum, map_zero]`. Simplify using `only [map_mul, d.emb_sH h c sg pt hpt σ hσ, eval₂_X] at h2`. Simplify `h2` using `only [RingHom.comp_apply]`.
-/
theorem emb_mem_ST (σ : OmS (Ω c) d.D d.N →+* ℂ) (hσ : σ.comp (d.KTtoS h c) = tauPev sg pt hpt) :
    σ.comp (algebraMap (Ω c) (OmS (Ω c) d.D d.N)) ∈ d.ST c sg (fun i j => pt (i.succ, j)) := by
  refine ⟨?_, fun i => ?_⟩
  · show (σ.comp (algebraMap (Ω c) (OmS (Ω c) d.D d.N))).comp (algebraMap K (Ω c)) = sg
    refine RingHom.ext fun a => ?_
    have h1 := d.emb_sH h c sg pt hpt σ hσ (C a)
    have h2 := (d.sH c).commutes a
    rw [MvPolynomial.algebraMap_eq] at h2
    rw [h2, eval₂_C] at h1
    rw [RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact h1
  · have h2 := congrArg σ (d.sH_rel hd c i)
    rw [map_sum, map_zero] at h2
    simp only [map_mul, d.emb_sH h c sg pt hpt σ hσ, eval₂_X] at h2
    simpa only [RingHom.comp_apply] using h2

/- English proof (translation)
Apply `IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (SVar d.D d.N) (Ω c)))` to reduce the goal to its premises. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[d.algC c a]`.

Conclude with `RingHom.congr_fun he a`. Introduce `v`. Establish `hs : ∀ p, σ₁ (d.sH c (X p)) = σ₂ (d.sH c (X p))`. Introduce `p`. Rewrite using `[← d.KTtoS_alg h c, ← RingHom.comp_apply, h₁, ← h₂, RingHom.comp_apply]`.

Simplify using `only [RingHom.comp_apply]`. Break down `v with ⟨⟩ | ⟨i, k⟩` into its components or cases. Establish `h0` using `hs (0, d.jc c)`. Simplify `h0` using `[d.sH_eq, sHp, pImg, sac_self]`. Establish `h0` using `hs (i, (d.jc c).succAbove k)`.

Simplify `h0` using `[d.sH_eq, sHp, pImg, sac_succAbove]`.
-/
theorem emb_ext (σ₁ σ₂ : OmS (Ω c) d.D d.N →+* ℂ) (h₁ : σ₁.comp (d.KTtoS h c) = tauPev sg pt hpt)
    (h₂ : σ₂.comp (d.KTtoS h c) = tauPev sg pt hpt)
    (he : σ₁.comp (algebraMap (Ω c) _) = σ₂.comp (algebraMap (Ω c) _)) : σ₁ = σ₂ := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (SVar d.D d.N) (Ω c)))
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply]
    rw [d.algC c a]
    exact RingHom.congr_fun he a
  · intro v
    have hs : ∀ p, σ₁ (d.sH c (X p)) = σ₂ (d.sH c (X p)) := by
      intro p
      rw [← d.KTtoS_alg h c, ← RingHom.comp_apply, h₁, ← h₂, RingHom.comp_apply]
    simp only [RingHom.comp_apply]
    rcases v with ⟨⟩ | ⟨i, k⟩
    · have h0 := hs (0, d.jc c)
      simpa [d.sH_eq, sHp, pImg, sac_self] using h0
    · have h0 := hs (i, (d.jc c).succAbove k)
      simpa [d.sH_eq, sHp, pImg, sac_succAbove] using h0

include hd h hpt in
/- English proof (translation)
Take `⟨hPT, hPeq⟩` from `hP`. Establish `hcomp : (d.evP c P pt).comp (d.sHp c).toRingHom = eval₂Hom sg pt` using `RingHom.ext fun q => d.evP_sHp c sg pt hd P hPT hPeq q`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `F hF`. Assume the negation of the conclusion as `hF0`.

Use `letI alg1 : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra`. Use `haveI := (d.omS_finite hd h c).1`. Use `letI alg2 : Algebra (KTp K d.D d.N) (OmS (Ω c) d.D d.N) := (d.sH c).toRingHom.toAlgebra`. Use `haveI : IsScalarTower (KTp K d.D d.N) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := IsScalarTower.of_algebraMap_eq fun q => (d.KTtoS_alg h c q).symm`. Establish `halg : IsAlgebraic (KTf K d.D d.N) (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) F)` using `Algebra.IsAlgebraic.isAlgebraic _`.

Rewrite `halg` using `[← IsFractionRing.isAlgebraic_iff (KTp K d.D d.N) (KTf K d.D d.N)]`. Take `⟨q, hq0, hq⟩` from `halg`. Establish `e : (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)).comp (d.sHp c).toRingHom = algebraMap (KTp K d.D d.N) (OmS (Ω c) d.D d.N)` using `RingHom.ext fun r => (d.sH_eq c r).symm`. Establish `hq' : Polynomial.eval₂ (d.sHp c).toRingHom F q = 0`. Apply `IsFractionRing.injective (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)` to reduce the goal to its premises.

Rewrite using `[map_zero, Polynomial.hom_eval₂, e, ← Polynomial.aeval_def, hq]`. Take `⟨q', hqq, hndvd⟩` from `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq0 0`. Simplify using `only [map_zero, sub_zero] at hqq hndvd`. Rewrite `hndvd` using `[Polynomial.X_dvd_iff]`. Rewrite `hq'` using `[hqq, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow]`.

Establish `hq'' : Polynomial.eval₂ (d.sHp c).toRingHom F q' = 0` using `(mul_eq_zero.mp hq').resolve_left (pow_ne_zero _ hF0)`. Establish `h3` using `congrArg (d.evP c P pt) hq''`. Rewrite `h3` using `[Polynomial.hom_eval₂, map_zero, hF, hcomp, Polynomial.eval₂_at_zero]`. Conclude with `hpt _ hndvd h3`.
-/
theorem evalAtPoint_injective (P : Ω c →+* ℂ) (hP : P ∈ d.ST c sg (fun i j => pt (i.succ, j))) :
    Function.Injective (d.evP c P pt) := by
  obtain ⟨hPT, hPeq⟩ := hP
  have hcomp : (d.evP c P pt).comp (d.sHp c).toRingHom = eval₂Hom sg pt :=
    RingHom.ext fun q => d.evP_sHp c sg pt hd P hPT hPeq q
  rw [injective_iff_map_eq_zero]
  intro F hF
  by_contra hF0
  letI alg1 : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI := (d.omS_finite hd h c).1
  letI alg2 : Algebra (KTp K d.D d.N) (OmS (Ω c) d.D d.N) := (d.sH c).toRingHom.toAlgebra
  haveI : IsScalarTower (KTp K d.D d.N) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    IsScalarTower.of_algebraMap_eq fun q => (d.KTtoS_alg h c q).symm

  have halg : IsAlgebraic (KTf K d.D d.N)
      (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) F) :=
    Algebra.IsAlgebraic.isAlgebraic _
  rw [← IsFractionRing.isAlgebraic_iff (KTp K d.D d.N) (KTf K d.D d.N)] at halg
  obtain ⟨q, hq0, hq⟩ := halg
  have e : (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)).comp
      (d.sHp c).toRingHom = algebraMap (KTp K d.D d.N) (OmS (Ω c) d.D d.N) :=
    RingHom.ext fun r => (d.sH_eq c r).symm
  have hq' : Polynomial.eval₂ (d.sHp c).toRingHom F q = 0 := by
    apply IsFractionRing.injective (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
    rw [map_zero, Polynomial.hom_eval₂, e, ← Polynomial.aeval_def, hq]

  obtain ⟨q', hqq, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq0 0
  simp only [map_zero, sub_zero] at hqq hndvd
  rw [Polynomial.X_dvd_iff] at hndvd
  rw [hqq, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow] at hq'
  have hq'' : Polynomial.eval₂ (d.sHp c).toRingHom F q' = 0 :=
    (mul_eq_zero.mp hq').resolve_left (pow_ne_zero _ hF0)
  have h3 := congrArg (d.evP c P pt) hq''
  rw [Polynomial.hom_eval₂, map_zero, hF, hcomp, Polynomial.eval₂_at_zero] at h3
  exact hpt _ hndvd h3

include hd in
/- English proof (translation)
Establish `hinj` using `d.evalAtPoint_injective hd h c sg pt hpt P hP`. Use `⟨IsFractionRing.lift (A := MvPolynomial (SVar d.D d.N) (Ω c)) (K := OmS (Ω c) d.D d.N) hinj, ?_, ?_⟩` and prove the remaining obligations. Apply `IsLocalization.ringHom_ext (nonZeroDivisors (KTp K d.D d.N))` to reduce the goal to its premises. Use `RingHom.ext fun q => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`.

Rewrite using `[d.KTtoS_alg h c q, tauPev_apply, d.sH_eq c q, IsFractionRing.lift_algebraMap]`. Conclude with `d.evP_sHp c sg pt hd P hP.1 hP.2 q`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, ← d.algC c a, IsFractionRing.lift_algebraMap]`. Simplify using `[evP]`.
-/
theorem exists_emb (P : Ω c →+* ℂ) (hP : P ∈ d.ST c sg (fun i j => pt (i.succ, j))) :
    ∃ σ : OmS (Ω c) d.D d.N →+* ℂ, σ.comp (d.KTtoS h c) = tauPev sg pt hpt ∧
      σ.comp (algebraMap (Ω c) (OmS (Ω c) d.D d.N)) = P := by
  have hinj := d.evalAtPoint_injective hd h c sg pt hpt P hP
  refine ⟨IsFractionRing.lift (A := MvPolynomial (SVar d.D d.N) (Ω c)) (K := OmS (Ω c) d.D d.N) hinj,
    ?_, ?_⟩
  · apply IsLocalization.ringHom_ext (nonZeroDivisors (KTp K d.D d.N))
    refine RingHom.ext fun q => ?_
    simp only [RingHom.comp_apply]
    rw [d.KTtoS_alg h c q, tauPev_apply, d.sH_eq c q, IsFractionRing.lift_algebraMap]
    exact d.evP_sHp c sg pt hd P hP.1 hP.2 q
  · refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, ← d.algC c a, IsFractionRing.lift_algebraMap]
    simp [evP]

include hd in
/- English proof (translation)
Use `letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra`. Use `letI : Algebra (KTf K d.D d.N) ℂ := (tauPev sg pt hpt).toAlgebra`. Establish `hcomm : ∀ σ : OmS (Ω c) d.D d.N →ₐ[KTf K d.D d.N] ℂ, (σ : OmS (Ω c) d.D d.N →+* ℂ).comp (d.KTtoS h c) = tauPev sg pt hpt` using `fun σ => RingHom.ext fun z => σ.commutes z`. Use `⟨fun σ₁ σ₂ he => ?_, ?_⟩` and prove the remaining obligations. Apply `AlgHom.coe_ringHom_injective` to reduce the goal to its premises.

Conclude with `d.emb_ext h c sg pt hpt _ _ (hcomm σ₁) (hcomm σ₂) he`. Use extensionality with `P`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨σ, rfl⟩`. Conclude with `d.emb_mem_ST hd h c sg pt hpt _ (hcomm σ)`.

Introduce `hP`. Take `⟨σ, h1, h2⟩` from `d.exists_emb hd h c sg pt hpt P hP`. Conclude with `⟨{ σ with commutes' := fun z => RingHom.congr_fun h1 z }, h2⟩`.
-/
theorem fibre_core :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    letI : Algebra (KTf K d.D d.N) ℂ := (tauPev sg pt hpt).toAlgebra
    Function.Injective (fun σ : OmS (Ω c) d.D d.N →ₐ[KTf K d.D d.N] ℂ =>
        (σ : OmS (Ω c) d.D d.N →+* ℂ).comp (algebraMap (Ω c) (OmS (Ω c) d.D d.N))) ∧
      Set.range (fun σ : OmS (Ω c) d.D d.N →ₐ[KTf K d.D d.N] ℂ =>
        (σ : OmS (Ω c) d.D d.N →+* ℂ).comp (algebraMap (Ω c) (OmS (Ω c) d.D d.N))) =
        d.ST c sg (fun i j => pt (i.succ, j)) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI : Algebra (KTf K d.D d.N) ℂ := (tauPev sg pt hpt).toAlgebra
  have hcomm : ∀ σ : OmS (Ω c) d.D d.N →ₐ[KTf K d.D d.N] ℂ,
      (σ : OmS (Ω c) d.D d.N →+* ℂ).comp (d.KTtoS h c) = tauPev sg pt hpt :=
    fun σ => RingHom.ext fun z => σ.commutes z
  refine ⟨fun σ₁ σ₂ he => ?_, ?_⟩
  · apply AlgHom.coe_ringHom_injective
    exact d.emb_ext h c sg pt hpt _ _ (hcomm σ₁) (hcomm σ₂) he
  · ext P
    constructor
    · rintro ⟨σ, rfl⟩
      exact d.emb_mem_ST hd h c sg pt hpt _ (hcomm σ)
    · intro hP
      obtain ⟨σ, h1, h2⟩ := d.exists_emb hd h c sg pt hpt P hP
      exact ⟨{ σ with commutes' := fun z => RingHom.congr_fun h1 z }, h2⟩

end emb

end Data

end ReciprocityTheory.ChartRestriction.G.T0
