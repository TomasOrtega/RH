import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittLam

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
  Formalism.L2.SG.Pf.NcS.KfOrbPf
open scoped TensorProduct

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM δ hδ hδ0`. Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `hσ : ∀ z, σ (σ z) = z` using `PI.VolStabS.sigma_invol σ hCM.2.2.2`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : E, σ x ≠ x := by`. Assume the negation of the conclusion as `H`.

Use `push Not at H`. Set `w : InfinitePlace E` to `Classical.arbitrary _`. Establish `hreal : ComplexEmbedding.IsReal w.embedding`. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `z`.

Rewrite using `[ComplexEmbedding.conjugate_coe_eq, ← Complex.star_def, ← hCM.2.2.2, H z]`. Conclude with `(InfinitePlace.not_isReal_iff_isComplex.2 (hCM.2.1.isComplex w)) (InfinitePlace.isReal_iff.2 hreal)`. Use `set θ : E := x - σ x with hθdef`. Establish `hσθ : σ θ = -θ` using `by rw [hθdef, map_sub, hσ]; ring`. Establish `hθ0 : θ ≠ 0` using `sub_ne_zero.2 (Ne.symm hx)`.

Establish `hind : ∀ p q : F, algebraMap F E p + algebraMap F E q * θ = 0 → p = 0 ∧ q = 0`. Introduce `p q h`. Establish `h'` using `congrArg σ h`. Rewrite `h'` using `[map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσθ, map_zero]`. Establish `hq : (2 : E) * (algebraMap F E q * θ) = 0` using `by linear_combination h - h'`.

Establish `hq0 : q = 0`. Break down `mul_eq_zero.1 ((mul_eq_zero.1 hq).resolve_left two_ne_zero) with h1 | h1` into its components or cases. Conclude with `(algebraMap F E).injective (by rw [h1, map_zero])`. Conclude with `absurd h1 hθ0`. Substitute `hq0` using the available equality.

Rewrite `h` using `[map_zero, zero_mul, add_zero]`. Conclude with `⟨(algebraMap F E).injective (by rw [h, map_zero]), rfl⟩`. Set `v2 : Fin 2 → E` to `![1, θ]`. Establish `hli : LinearIndependent F v2`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `g hg`. Rewrite `hg` using `[Fin.sum_univ_two]`. Establish `e : algebraMap F E (g 0) + algebraMap F E (g 1) * θ = 0`. Rewrite using `[← hg]`. Simplify using `[v2, Algebra.smul_def]`.

Take `⟨h0, h1⟩` from `hind _ _ e`. Introduce `i`. Use `fin_cases i`. Conclude with `h0`. Conclude with `h1`.

Set `b2 : Module.Basis (Fin 2) F E` to `basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hCM.2.2.1])`. Establish `hb2 : ∀ i, b2 i = v2 i` using `fun i => by`. Simplify using `only [b2, coe_basisOfLinearIndependentOfCardEqFinrank]`. Establish `hdec : ∀ e : E, e = algebraMap F E (b2.repr e 0) + algebraMap F E (b2.repr e 1) * θ`. Introduce `e`.

Use `conv_lhs => rw [← b2.sum_repr e]`. Rewrite using `[Fin.sum_univ_two, hb2, hb2]`. Simplify using `[v2, Algebra.smul_def]`. Establish `hfixF : ∀ e : E, σ e = e → e = algebraMap F E (b2.repr e 0)`. Introduce `e he`.

Establish `h1` using `hdec e`. Establish `h2` using `congrArg σ h1`. Rewrite `h2` using `[he, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσθ]`. Establish `h3 : algebraMap F E 0 + algebraMap F E (2 * b2.repr e 1) * θ = 0`. Rewrite using `[map_zero, map_mul, map_ofNat]`.

Take the linear combination `h2 - h1`. Establish `hq` using `(hind _ _ h3).2`. Establish `hq' : b2.repr e 1 = 0` using `(mul_eq_zero.1 hq).resolve_left two_ne_zero`. Rewrite `h1` using `[hq', map_zero (algebraMap F E), zero_mul, add_zero]`. Conclude with `h1`.

Establish `hθ2σ : σ (θ ^ 2) = θ ^ 2` using `by rw [map_pow, hσθ, neg_sq]`. Use `set d := b2.repr (θ ^ 2) 0 with hd_def`. Establish `hd : θ ^ 2 = algebraMap F E d` using `hfixF _ hθ2σ`. Establish `hd0 : d ≠ 0`. Introduce `h`.

Rewrite `hd` using `[h, map_zero]`. Conclude with `hθ0 ((pow_eq_zero_iff two_ne_zero).1 hd)`. Establish `hd1 : d ≠ 1`. Introduce `h`. Rewrite `hd` using `[h, map_one]`.

Establish `h1 : (θ - 1) * (θ + 1) = 0` using `by linear_combination hd`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Establish `e : θ = 1` using `sub_eq_zero.1 h`. Rewrite `hσθ` using `[e, map_one]`. Conclude with `two_ne_zero (by linear_combination hσθ : (2 : E) = 0)`.

Establish `e : θ = -1` using `eq_neg_of_add_eq_zero_left h`. Rewrite `hσθ` using `[e, map_neg, map_one]`. Conclude with `two_ne_zero (by linear_combination -hσθ : (2 : E) = 0)`. Use `set β0 := b2.repr δ 0 with hβ0_def`. Establish `hδF : δ = algebraMap F E β0` using `hfixF δ hδ`.

Establish `hβ0 : β0 ≠ 0`. Introduce `h`. Rewrite `hδF` using `[h, map_zero]`. Conclude with `hδ0 hδF`. Establish `h1d : (1 - d) ≠ 0` using `sub_ne_zero.2 (Ne.symm hd1)`.

Use `set Pc : F := (1 + d) / (1 - d) with hPc`. Use `set Qc : F := 2 / (1 - d) with hQc_def`. Establish `hQc : Qc ≠ 0` using `div_ne_zero two_ne_zero h1d`. Establish `hpq : Pc ^ 2 - d * Qc ^ 2 = 1`. Rewrite using `[hPc, hQc_def]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `filter_upwards [ev_int (F := F) d, ev_int (F := F) β0, ev_int (F := F) β0⁻¹, ev_int (F := F) Pc, ev_int (F := F) Qc, ev_int (F := F) (Qc * d)⁻¹, ev_int (F := F) (4 : F)⁻¹, ev_oev (F := F) θ, ev_crd_oev b2] with v hdv hβv hβiv hPv hQv hKv h4v hθv hcrd`. Introduce `t ht`. Set `ι : v.adicCompletionIntegers F →+* Fv F v ⊗[F] E` to `(algebraMap (Fv F v) (Fv F v ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype`.

Establish `hιF : ∀ (y : F) (hy : algebraMap F (Fv F v) y ∈ v.adicCompletionIntegers F), ι ⟨_, hy⟩ = algebraMap F (Fv F v ⊗[F] E) y`. Introduce `y hy`. Use `show algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) y) = _`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Establish `hιO : ∀ r, ι r ∈ oevRing (E` using `E) v := by`.

Introduce `r`. Use `show algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) ∈ OEv (E := E) v`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `oev_smul' v r.2 (oev_one v)`. Establish `hsι : ∀ r, sigR (Fv F v) σ (ι r) = ι r`.

Introduce `r`. Use `show sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v)) = _`. Simplify using `[sigR, Algebra.TensorProduct.algebraMap_apply]`. Both sides reduce to the same expression. Establish `hincl : ∀ y : F, inclR (F` using `F) (Fv F v) (algebraMap F E y) = algebraMap F (Fv F v ⊗[F] E) y := fun y => (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).commutes y`.

Establish `hΘ : (inclR (F` using `F) (Fv F v) θ) ^ 2 = ι ⟨_, hdv⟩ := by`. Rewrite using `[hιF, ← map_pow, hd, hincl]`. Establish `hsΘ : sigR (Fv F v) σ (inclR (F` using `F) (Fv F v) θ) = -inclR (F := F) (Fv F v) θ := by`. Simplify using `[sigR, inclR, hσθ, TensorProduct.tmul_neg]`. Establish `hcrd'` using `hcrd t ht`.

Establish `htd : t = ι ⟨_, hcrd' 0⟩ + ι ⟨_, hcrd' 1⟩ * inclR (F` using `F) (Fv F v) θ := by conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b2).sum_repr t]`. Rewrite using `[Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, hb2, hb2]`. Use `show _ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (PI.VolStabS.PositiveNearLattice.crd b2 (Fv F v) t 0) + algebraMap (Fv F v) (Fv F v ⊗[F] E) (PI.VolStabS.PositiveNearLattice.crd b2 (Fv F v) t 1) * inclR (F := F) (Fv F v) θ`. Simplify using `only [PI.VolStabS.PositiveNearLattice.crd, Algebra.smul_def, v2, Matrix.cons_val_zero, Matrix.cons_val_one]`. Simplify using `[inclR]`.

Establish `hPQ : (⟨_, hPv⟩ : v.adicCompletionIntegers F) ^ 2 - ⟨_, hdv⟩ * ⟨_, hQv⟩ ^ 2 = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (algebraMap F (Fv F v) Pc) ^ 2 - algebraMap F (Fv F v) d * (algebraMap F (Fv F v) Qc) ^ 2 = 1`. Rewrite using `[← map_pow, ← map_pow, ← map_mul, ← map_sub, hpq, map_one]`. Establish `hB : (⟨_, hβv⟩ : v.adicCompletionIntegers F) * ⟨_, hβiv⟩ = 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show algebraMap F (Fv F v) β0 * algebraMap F (Fv F v) β0⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel₀ hβ0, map_one]`. Establish `hK : (⟨_, hQv⟩ : v.adicCompletionIntegers F) * ⟨_, hdv⟩ * ⟨_, hKv⟩ = 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show algebraMap F (Fv F v) Qc * algebraMap F (Fv F v) d * algebraMap F (Fv F v) (Qc * d)⁻¹ = 1`. Rewrite using `[← map_mul, ← map_mul, mul_inv_cancel₀ (mul_ne_zero hQc hd0), map_one]`. Establish `h4 : (4 : v.adicCompletionIntegers F) * ⟨_, h4v⟩ = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((4 : v.adicCompletionIntegers F) : Fv F v) * algebraMap F (Fv F v) (4 : F)⁻¹ = 1`.

Establish `e4 : ((4 : v.adicCompletionIntegers F) : Fv F v) = algebraMap F (Fv F v) 4`. Rewrite using `[map_ofNat]`. Both sides reduce to the same expression. Rewrite using `[e4, ← map_mul, mul_inv_cancel₀ (by norm_num), map_one]`. Take `⟨lam, hlamO, hlam, c', hc'O, hc'⟩` from `core_loc ι (sigR (Fv F v) σ) (oevRing (E := E) v) hιO (inclR (F := F) (Fv F v) θ) hθv ⟨_, hdv⟩ ⟨_, hβv⟩ ⟨_, hPv⟩ ⟨_, hQv⟩ ⟨_, hcrd' 0⟩ ⟨_, hcrd' 1⟩ hΘ hsΘ hsι hPQ ⟨_, hβiv⟩ ⟨_, hKv⟩ ⟨_, h4v⟩ hB hK h4`.

Use `⟨lam, hlamO, hlam, c', hc'O, ?_⟩` and prove the remaining obligations. Establish `hδι : inclR (F` using `F) (Fv F v) δ = ι ⟨_, hβv⟩ := by rw [hιF, hδF, hincl]`. Rewrite using `[hδι]`. Use `conv_lhs => rw [htd]`. Conclude with `hc'`.
-/
theorem lamAE : LamAE := by
  intro F E _ _ _ _ _ σ hCM δ hδ hδ0
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hσ : ∀ z, σ (σ z) = z := PI.VolStabS.sigma_invol σ hCM.2.2.2
  obtain ⟨x, hx⟩ : ∃ x : E, σ x ≠ x := by
    by_contra H
    push Not at H
    let w : InfinitePlace E := Classical.arbitrary _
    have hreal : ComplexEmbedding.IsReal w.embedding := by
      rw [ComplexEmbedding.isReal_iff]
      ext z
      rw [ComplexEmbedding.conjugate_coe_eq, ← Complex.star_def, ← hCM.2.2.2, H z]
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (hCM.2.1.isComplex w)) (InfinitePlace.isReal_iff.2 hreal)
  set θ : E := x - σ x with hθdef
  have hσθ : σ θ = -θ := by rw [hθdef, map_sub, hσ]; ring
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hind : ∀ p q : F, algebraMap F E p + algebraMap F E q * θ = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    have h' := congrArg σ h
    rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσθ, map_zero] at h'
    have hq : (2 : E) * (algebraMap F E q * θ) = 0 := by linear_combination h - h'
    have hq0 : q = 0 := by
      rcases mul_eq_zero.1 ((mul_eq_zero.1 hq).resolve_left two_ne_zero) with h1 | h1
      · exact (algebraMap F E).injective (by rw [h1, map_zero])
      · exact absurd h1 hθ0
    subst hq0
    rw [map_zero, zero_mul, add_zero] at h
    exact ⟨(algebraMap F E).injective (by rw [h, map_zero]), rfl⟩
  let v2 : Fin 2 → E := ![1, θ]
  have hli : LinearIndependent F v2 := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_two] at hg
    have e : algebraMap F E (g 0) + algebraMap F E (g 1) * θ = 0 := by
      rw [← hg]; simp [v2, Algebra.smul_def]
    obtain ⟨h0, h1⟩ := hind _ _ e
    intro i
    fin_cases i
    · exact h0
    · exact h1
  let b2 : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hCM.2.2.1])
  have hb2 : ∀ i, b2 i = v2 i := fun i => by
    simp only [b2, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hdec : ∀ e : E, e = algebraMap F E (b2.repr e 0) + algebraMap F E (b2.repr e 1) * θ := by
    intro e
    conv_lhs => rw [← b2.sum_repr e]
    rw [Fin.sum_univ_two, hb2, hb2]
    simp [v2, Algebra.smul_def]

  have hfixF : ∀ e : E, σ e = e → e = algebraMap F E (b2.repr e 0) := by
    intro e he
    have h1 := hdec e
    have h2 := congrArg σ h1
    rw [he, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσθ] at h2
    have h3 : algebraMap F E 0 + algebraMap F E (2 * b2.repr e 1) * θ = 0 := by
      rw [map_zero, map_mul, map_ofNat]; linear_combination h2 - h1
    have hq := (hind _ _ h3).2
    have hq' : b2.repr e 1 = 0 := (mul_eq_zero.1 hq).resolve_left two_ne_zero
    rw [hq', map_zero (algebraMap F E), zero_mul, add_zero] at h1
    exact h1
  have hθ2σ : σ (θ ^ 2) = θ ^ 2 := by rw [map_pow, hσθ, neg_sq]
  set d := b2.repr (θ ^ 2) 0 with hd_def
  have hd : θ ^ 2 = algebraMap F E d := hfixF _ hθ2σ
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, map_zero] at hd
    exact hθ0 ((pow_eq_zero_iff two_ne_zero).1 hd)
  have hd1 : d ≠ 1 := by
    intro h
    rw [h, map_one] at hd
    have h1 : (θ - 1) * (θ + 1) = 0 := by linear_combination hd
    rcases mul_eq_zero.1 h1 with h | h
    · have e : θ = 1 := sub_eq_zero.1 h
      rw [e, map_one] at hσθ
      exact two_ne_zero (by linear_combination hσθ : (2 : E) = 0)
    · have e : θ = -1 := eq_neg_of_add_eq_zero_left h
      rw [e, map_neg, map_one] at hσθ
      exact two_ne_zero (by linear_combination -hσθ : (2 : E) = 0)
  set β0 := b2.repr δ 0 with hβ0_def
  have hδF : δ = algebraMap F E β0 := hfixF δ hδ
  have hβ0 : β0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hδF
    exact hδ0 hδF
  have h1d : (1 - d) ≠ 0 := sub_ne_zero.2 (Ne.symm hd1)
  set Pc : F := (1 + d) / (1 - d) with hPc
  set Qc : F := 2 / (1 - d) with hQc_def
  have hQc : Qc ≠ 0 := div_ne_zero two_ne_zero h1d
  have hpq : Pc ^ 2 - d * Qc ^ 2 = 1 := by
    rw [hPc, hQc_def]
    field_simp
    ring
  filter_upwards [ev_int (F := F) d, ev_int (F := F) β0, ev_int (F := F) β0⁻¹, ev_int (F := F) Pc,
    ev_int (F := F) Qc, ev_int (F := F) (Qc * d)⁻¹, ev_int (F := F) (4 : F)⁻¹, ev_oev (F := F) θ, ev_crd_oev b2]
    with v hdv hβv hβiv hPv hQv hKv h4v hθv hcrd
  intro t ht
  let ι : v.adicCompletionIntegers F →+* Fv F v ⊗[F] E :=
    (algebraMap (Fv F v) (Fv F v ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype
  have hιF : ∀ (y : F) (hy : algebraMap F (Fv F v) y ∈ v.adicCompletionIntegers F),
      ι ⟨_, hy⟩ = algebraMap F (Fv F v ⊗[F] E) y := by
    intro y hy
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) y) = _
    rw [← IsScalarTower.algebraMap_apply]
  have hιO : ∀ r, ι r ∈ oevRing (E := E) v := by
    intro r
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) ∈ OEv (E := E) v
    rw [Algebra.algebraMap_eq_smul_one]
    exact oev_smul' v r.2 (oev_one v)
  have hsι : ∀ r, sigR (Fv F v) σ (ι r) = ι r := by
    intro r
    show sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v)) = _
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hincl : ∀ y : F, inclR (F := F) (Fv F v) (algebraMap F E y) = algebraMap F (Fv F v ⊗[F] E) y :=
    fun y => (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).commutes y
  have hΘ : (inclR (F := F) (Fv F v) θ) ^ 2 = ι ⟨_, hdv⟩ := by
    rw [hιF, ← map_pow, hd, hincl]
  have hsΘ : sigR (Fv F v) σ (inclR (F := F) (Fv F v) θ) = -inclR (F := F) (Fv F v) θ := by
    simp [sigR, inclR, hσθ, TensorProduct.tmul_neg]
  have hcrd' := hcrd t ht
  have htd : t = ι ⟨_, hcrd' 0⟩ + ι ⟨_, hcrd' 1⟩ * inclR (F := F) (Fv F v) θ := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b2).sum_repr t]
    rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, hb2, hb2]
    show _ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (PI.VolStabS.PositiveNearLattice.crd b2 (Fv F v) t 0) +
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (PI.VolStabS.PositiveNearLattice.crd b2 (Fv F v) t 1) * inclR (F := F) (Fv F v) θ
    simp only [PI.VolStabS.PositiveNearLattice.crd, Algebra.smul_def, v2, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp [inclR]
  have hPQ : (⟨_, hPv⟩ : v.adicCompletionIntegers F) ^ 2 - ⟨_, hdv⟩ * ⟨_, hQv⟩ ^ 2 = 1 := by
    apply Subtype.ext
    show (algebraMap F (Fv F v) Pc) ^ 2 - algebraMap F (Fv F v) d * (algebraMap F (Fv F v) Qc) ^ 2 = 1
    rw [← map_pow, ← map_pow, ← map_mul, ← map_sub, hpq, map_one]
  have hB : (⟨_, hβv⟩ : v.adicCompletionIntegers F) * ⟨_, hβiv⟩ = 1 := by
    apply Subtype.ext
    show algebraMap F (Fv F v) β0 * algebraMap F (Fv F v) β0⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hβ0, map_one]
  have hK : (⟨_, hQv⟩ : v.adicCompletionIntegers F) * ⟨_, hdv⟩ * ⟨_, hKv⟩ = 1 := by
    apply Subtype.ext
    show algebraMap F (Fv F v) Qc * algebraMap F (Fv F v) d * algebraMap F (Fv F v) (Qc * d)⁻¹ = 1
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (mul_ne_zero hQc hd0), map_one]
  have h4 : (4 : v.adicCompletionIntegers F) * ⟨_, h4v⟩ = 1 := by
    apply Subtype.ext
    show ((4 : v.adicCompletionIntegers F) : Fv F v) * algebraMap F (Fv F v) (4 : F)⁻¹ = 1
    have e4 : ((4 : v.adicCompletionIntegers F) : Fv F v) = algebraMap F (Fv F v) 4 := by
      rw [map_ofNat]; rfl
    rw [e4, ← map_mul, mul_inv_cancel₀ (by norm_num), map_one]
  obtain ⟨lam, hlamO, hlam, c', hc'O, hc'⟩ := core_loc ι (sigR (Fv F v) σ) (oevRing (E := E) v) hιO
    (inclR (F := F) (Fv F v) θ) hθv ⟨_, hdv⟩ ⟨_, hβv⟩ ⟨_, hPv⟩ ⟨_, hQv⟩ ⟨_, hcrd' 0⟩ ⟨_, hcrd' 1⟩
    hΘ hsΘ hsι hPQ ⟨_, hβiv⟩ ⟨_, hKv⟩ ⟨_, h4v⟩ hB hK h4
  refine ⟨lam, hlamO, hlam, c', hc'O, ?_⟩
  have hδι : inclR (F := F) (Fv F v) δ = ι ⟨_, hβv⟩ := by rw [hιF, hδF, hincl]
  rw [hδι]
  conv_lhs => rw [htd]
  exact hc'

end Formalism.L2.SG.Pf.NcS.IntWittPf
