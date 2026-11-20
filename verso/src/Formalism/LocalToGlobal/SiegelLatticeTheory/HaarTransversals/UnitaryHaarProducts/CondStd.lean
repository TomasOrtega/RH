import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.StdChar
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology Filter

namespace Formalism.L2.SG.Pf.CondStd

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Take `⟨m, hm, hma⟩` from `PIW.AdelClassFin.DictRing.af_denom a`. Take `⟨β, y, hy, hβ⟩` from `PIW.AdelClassFin.DictRing.af_approx _ hma m hm`. Use `⟨(β : F) / m, ?_⟩` and prove the remaining obligations. Establish `hmF : (m : F) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `hcast : ((m : ℕ) : Af F) = algebraMap F (Af F) (m : F)` using `(map_natCast _ m).symm`.

Establish `hu : IsUnit ((m : ℕ) : Af F)`. Rewrite using `[hcast]`. Conclude with `(isUnit_iff_ne_zero.2 hmF).map _`. Establish `e1 : ((m : ℕ) : Af F) * (a - algebraMap F (Af F) ((β : F) / m)) = (m : Af F) * y`. Rewrite using `[mul_sub, hβ, hcast, ← map_mul, mul_div_cancel₀ _ hmF, IsScalarTower.algebraMap_apply (𝓞 F) F (Af F)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hu.mul_left_cancel e1]`. Conclude with `hy`.
-/
theorem fin_approx (a : Af F) : ∃ x : F, a - algebraMap F (Af F) x ∈ Formalism.UG.intAd F := by
  obtain ⟨m, hm, hma⟩ := PIW.AdelClassFin.DictRing.af_denom a
  obtain ⟨β, y, hy, hβ⟩ := PIW.AdelClassFin.DictRing.af_approx _ hma m hm
  refine ⟨(β : F) / m, ?_⟩
  have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  have hcast : ((m : ℕ) : Af F) = algebraMap F (Af F) (m : F) := (map_natCast _ m).symm
  have hu : IsUnit ((m : ℕ) : Af F) := by
    rw [hcast]
    exact (isUnit_iff_ne_zero.2 hmF).map _
  have e1 : ((m : ℕ) : Af F) * (a - algebraMap F (Af F) ((β : F) / m)) = (m : Af F) * y := by
    rw [mul_sub, hβ, hcast, ← map_mul, mul_div_cancel₀ _ hmF,
      IsScalarTower.algebraMap_apply (𝓞 F) F (Af F)]
    ring
  rw [hu.mul_left_cancel e1]
  exact hy

/- English proof (translation)
Introduce `a`. Rewrite using `[mem_closure_iff_nhds]`. Introduce `t ht`. Establish `hV : (fun w => a - w) ⁻¹' t ∈ 𝓝 (0 : Af F)`. Use `(continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations.

Simplify using `using ht`. Take `⟨N, hN, hNV⟩` from `Formalism.L2.SG.Pf.top_nhds_basis F _ hV`. Take `⟨m, hm, hma⟩` from `PIW.AdelClassFin.DictRing.af_denom a`. Take `⟨β, y, hy, hβ⟩` from `PIW.AdelClassFin.DictRing.af_approx _ hma (m * N) (Nat.mul_pos hm hN)`. Establish `hmF : (m : F) ≠ 0` using `by exact_mod_cast hm.ne'`.

Establish `hcast : ((m : ℕ) : Af F) = algebraMap F (Af F) (m : F)` using `(map_natCast _ m).symm`. Establish `hu : IsUnit ((m : ℕ) : Af F)`. Rewrite using `[hcast]`. Conclude with `(isUnit_iff_ne_zero.2 hmF).map _`. Establish `e1 : ((m : ℕ) : Af F) * (a - (N : Af F) * y) = ((m : ℕ) : Af F) * algebraMap F (Af F) ((β : F) / m)`.

Rewrite using `[mul_sub, hβ, hcast, ← map_mul, mul_div_cancel₀ _ hmF, IsScalarTower.algebraMap_apply (𝓞 F) F (Af F)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2` using `hu.mul_left_cancel e1`. Use `⟨algebraMap F (Af F) ((β : F) / m), ?_, ⟨_, rfl⟩⟩` and prove the remaining obligations.

Rewrite using `[← e2]`. Conclude with `hNV y hy`.
-/
theorem dense_F : DenseRange (algebraMap F (Af F)) := by
  intro a
  rw [mem_closure_iff_nhds]
  intro t ht
  have hV : (fun w => a - w) ⁻¹' t ∈ 𝓝 (0 : Af F) := by
    refine (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds ?_
    simpa using ht
  obtain ⟨N, hN, hNV⟩ := Formalism.L2.SG.Pf.top_nhds_basis F _ hV
  obtain ⟨m, hm, hma⟩ := PIW.AdelClassFin.DictRing.af_denom a
  obtain ⟨β, y, hy, hβ⟩ := PIW.AdelClassFin.DictRing.af_approx _ hma (m * N) (Nat.mul_pos hm hN)
  have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  have hcast : ((m : ℕ) : Af F) = algebraMap F (Af F) (m : F) := (map_natCast _ m).symm
  have hu : IsUnit ((m : ℕ) : Af F) := by
    rw [hcast]
    exact (isUnit_iff_ne_zero.2 hmF).map _
  have e1 : ((m : ℕ) : Af F) * (a - (N : Af F) * y) = ((m : ℕ) : Af F) * algebraMap F (Af F) ((β : F) / m) := by
    rw [mul_sub, hβ, hcast, ← map_mul, mul_div_cancel₀ _ hmF, IsScalarTower.algebraMap_apply (𝓞 F) F (Af F)]
    push_cast
    ring
  have e2 := hu.mul_left_cancel e1
  refine ⟨algebraMap F (Af F) ((β : F) / m), ?_, ⟨_, rfl⟩⟩
  rw [← e2]
  exact hNV y hy

variable [IsTotallyReal F]

open Formalism.L2.SG.Pf.StdChar in

/- English proof (translation)
Take `⟨hcont, -, htriv, -⟩` from `h1`. Establish `hinf : ∀ y : Ainf F, ψ (pairA F y 0) = psiA F y` using `fun y => h2 y`. Establish `hA : ∀ a : F, psiA F (algebraMap F (Ainf F) a) = Complex.exp (2 * Real.pi * Complex.I * ((trR F a : ℝ) : ℂ))`. Introduce `a`. Establish `hw : ∀ w : InfinitePlace F, InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ainf F) a) w) = w.embedding a`.

Introduce `w`. Use `first`. Consider the case `exact InfinitePlace.Completion.extensionEmbedding_coe w a`. Consider the case `exact InfinitePlace.Completion.extensionEmbedding_coe a`. Consider the case `simp [InfiniteAdeleRing]`.

Simplify using `only [psiA, hw]`. Use `first`. Consider the case `rfl`. Consider the case `simp [trR]`. Establish `hsplit : ∀ z : AF F, z = pairA F z.1 0 + pairA F 0 z.2`.

Introduce `z`. Use `first`. Consider the case `exact Prod.ext (add_zero _).symm (zero_add _).symm`. Consider the case `(show z = (z.1 + 0, 0 + z.2); rw [add_zero, zero_add]; rfl)`. Consider the case `(simp [pairA]; done)`.

Establish `hF : ∀ a : F, ψ (pairA F 0 (algebraMap F (Af F) a)) = psiFin F (algebraMap F (Af F) a)`. Introduce `a`. Establish `e2 : algebraMap F (AF F) a = pairA F (algebraMap F (Ainf F) a) 0 + pairA F 0 (algebraMap F (Af F) a)` using `by first`. Consider the case `exact hsplit _`. Consider the case `(rw [hsplit (algebraMap F (AF F) a)]; rfl)`.

Consider the case `simp [pairA]`. Establish `h3 : psiA F (algebraMap F (Ainf F) a) * ψ (pairA F 0 (algebraMap F (Af F) a)) = 1`. Rewrite using `[← hinf, ← AddChar.map_add_eq_mul, ← e2]`. Conclude with `htriv a`. Rewrite using `[psiFin_alg, Complex.exp_neg, ← hA a]`.

Conclude with `eq_inv_of_mul_eq_one_right h3`. Establish `hp : Continuous (fun z : Af F => pairA F 0 z)` using `by first`. Consider the case `exact continuous_const.prodMk continuous_id`. Consider the case `exact continuous_const.prod_mk continuous_id`. Consider the case `(unfold pairA; fun_prop)`.

Establish `hc : Continuous (fun z : Af F => ψ (pairA F 0 z))` using `hcont.comp hp`. Establish `hcf : Continuous (psiFin F)` using `by first`. Consider the case `exact continuous_psiFin F`. Consider the case `exact continuous_psiFin`. Consider the case `exact continuous_psiFin (F := F)`.

Establish `hfin : (fun z : Af F => ψ (pairA F 0 z)) = psiFin F` using `(dense_F (F := F)).equalizer hc hcf (funext fun a => hF a)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_psiStd (ψ : AddChar (AF F) ℂ) (h1 : IsCharAF F ψ) (h2 : Formalism.L2.SG.LocVol.IsStdChar ψ) (x : AF F) :
    ψ x = psiStd F x := by
  obtain ⟨hcont, -, htriv, -⟩ := h1
  have hinf : ∀ y : Ainf F, ψ (pairA F y 0) = psiA F y := fun y => h2 y
  have hA : ∀ a : F, psiA F (algebraMap F (Ainf F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((trR F a : ℝ) : ℂ)) := by
    intro a
    have hw : ∀ w : InfinitePlace F, InfinitePlace.Completion.extensionEmbedding w
        ((algebraMap F (Ainf F) a) w) = w.embedding a := by
      intro w
      first
        | exact InfinitePlace.Completion.extensionEmbedding_coe w a
        | exact InfinitePlace.Completion.extensionEmbedding_coe a
        | simp [InfiniteAdeleRing]
    simp only [psiA, hw]
    first
      | rfl
      | simp [trR]
  have hsplit : ∀ z : AF F, z = pairA F z.1 0 + pairA F 0 z.2 := by
    intro z
    first
      | exact Prod.ext (add_zero _).symm (zero_add _).symm
      | (show z = (z.1 + 0, 0 + z.2); rw [add_zero, zero_add]; rfl)
      | (simp [pairA]; done)
  have hF : ∀ a : F, ψ (pairA F 0 (algebraMap F (Af F) a)) = psiFin F (algebraMap F (Af F) a) := by
    intro a
    have e2 : algebraMap F (AF F) a =
        pairA F (algebraMap F (Ainf F) a) 0 + pairA F 0 (algebraMap F (Af F) a) := by
      first
        | exact hsplit _
        | (rw [hsplit (algebraMap F (AF F) a)]; rfl)
        | simp [pairA]
    have h3 : psiA F (algebraMap F (Ainf F) a) * ψ (pairA F 0 (algebraMap F (Af F) a)) = 1 := by
      rw [← hinf, ← AddChar.map_add_eq_mul, ← e2]
      exact htriv a
    rw [psiFin_alg, Complex.exp_neg, ← hA a]
    exact eq_inv_of_mul_eq_one_right h3
  have hp : Continuous (fun z : Af F => pairA F 0 z) := by
    first
      | exact continuous_const.prodMk continuous_id
      | exact continuous_const.prod_mk continuous_id
      | (unfold pairA; fun_prop)
  have hc : Continuous (fun z : Af F => ψ (pairA F 0 z)) := hcont.comp hp
  have hcf : Continuous (psiFin F) := by
    first
      | exact continuous_psiFin F
      | exact continuous_psiFin
      | exact continuous_psiFin (F := F)
  have hfin : (fun z : Af F => ψ (pairA F 0 z)) = psiFin F :=
    (dense_F (F := F)).equalizer hc hcf (funext fun a => hF a)
  calc ψ x = ψ (pairA F x.1 0 + pairA F 0 x.2) := by rw [← hsplit x]
    _ = ψ (pairA F x.1 0) * ψ (pairA F 0 x.2) := AddChar.map_add_eq_mul ψ _ _
    _ = psiA F x.1 * psiFin F x.2 := by rw [hinf, ← congrFun hfin x.2]
    _ = psiStd F x := rfl

end Formalism.L2.SG.Pf.CondStd

namespace Formalism.L2.SG.Pf.CondStd

def LocTrDual : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v),
    (∀ y ∈ v.adicCompletionIntegers F, ∀ q : F,
        singleV F v (x * y) - algebraMap F (Af F) q ∈ Formalism.UG.intAd F → ∃ n : ℤ, Algebra.trace ℚ F q = n) ↔
      Formalism.L2.SG.LocVol.dV v * x ∈ v.adicCompletionIntegers F

open Formalism.L2.SG.Pf.StdChar in

/- English proof (translation)
Establish `htr : ∀ q : F, trR F q = ((Algebra.trace ℚ F q : ℚ) : ℝ)`. Introduce `q`. Establish `hsum : ((Algebra.trace ℚ F q : ℚ) : ℂ) = ∑ σ : F →ₐ[ℚ] ℂ, σ q`. Establish `h : algebraMap ℚ ℂ (Algebra.trace ℚ F q) = ∑ σ : F →ₐ[ℚ] ℂ, σ q` using `by first`. Consider the case `exact trace_eq_sum_embeddings ℂ (x := q)`.

Consider the case `exact trace_eq_sum_embeddings (E := ℂ) (x := q)`. Consider the case `exact trace_eq_sum_embeddings ℂ q`. Consider the case `exact trace_eq_sum_embeddings (L := F) ℂ`. Rewrite using `[← h]`. Use `first`.

Consider the case `rfl`. Consider the case `(simp; done)`. Consider the case `exact (eq_ratCast _ _).symm`. Establish `hbij : Function.Bijective (fun w : InfinitePlace F => w.embedding.toRatAlgHom)`. Prove the components needed by the constructor for the conclusion.

Introduce `w w' h`. Establish `h' : w.embedding = w'.embedding`. Use extensionality with `z`. Conclude with `DFunLike.congr_fun h z`. Rewrite using `[← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h']`.

Introduce `σ`. Use `⟨InfinitePlace.mk σ.toRingHom, ?_⟩` and prove the remaining obligations. Establish `hr : ComplexEmbedding.IsReal (InfinitePlace.mk σ.toRingHom).embedding` using `InfinitePlace.isReal_iff.mp (IsTotallyReal.isReal _)`. Establish `he : (InfinitePlace.mk σ.toRingHom).embedding = σ.toRingHom`. Break down `InfinitePlace.embedding_mk_eq σ.toRingHom with h | h` into its components or cases.

Conclude with `h`. Rewrite `hr`, the goal using `[h]`. Establish `h2 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ.toRingHom) = ComplexEmbedding.conjugate σ.toRingHom` using `hr`. Use `first`. Consider the case `exact ComplexEmbedding.isReal_conjugate_iff.mp hr`.

Consider the case `(simp only [ComplexEmbedding.conjugate, star_star] at h2; exact h2.symm)`. Consider the case `(rw [star_star] at h2; exact h2.symm)`. Consider the case `(have h3 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ.toRingHom) = σ.toRingHom := RingHom.ext fun z => by simp [ComplexEmbedding.conjugate_coe_eq]`. Rewrite `h2` using `[h3]`. Conclude with `h2.symm)`.

Apply `AlgHom.ext` to reduce the goal to its premises. Introduce `z`. Use `show (InfinitePlace.mk σ.toRingHom).embedding z = σ z`. Rewrite using `[he]`. Both sides reduce to the same expression.

Establish `hs : ∑ w : InfinitePlace F, w.embedding q = ∑ σ : F →ₐ[ℚ] ℂ, σ q` using `Fintype.sum_bijective _ hbij _ _ (fun w => rfl)`. Establish `hre : trR F q = (∑ w : InfinitePlace F, w.embedding q).re`. Rewrite using `[Complex.re_sum]`. Both sides reduce to the same expression. Rewrite using `[hre, hs, ← hsum]`.

Use `first`. Consider the case `simp`. Consider the case `exact Complex.ratCast_re _`. Establish `hψ : ∀ z, ψ z = psiStd F z` using `fun z => eq_psiStd ψ h1 h2 z`. Establish `hV : ∀ y : Fv F v, psiV F ψ v y = psiFin F (singleV F v y)`.

Introduce `y`. Use `show ψ (pairA F 0 (singleV F v y)) = _`. Rewrite using `[hψ]`. Use `show psiA F 0 * psiFin F (singleV F v y) = _`. Rewrite using `[psiA_zero, one_mul]`.

Establish `hint : ∀ c ∈ Formalism.UG.intAd F, psiFin F c = 1`. Introduce `c hc`. Use `show ((AddCircle.toCircle (-((exists_psiF F).choose c)) : Circle) : ℂ) = 1`. Rewrite using `[(exists_psiF F).choose_spec.1 c hc, neg_zero]`. Use `first`.

Consider the case `simp`. Consider the case `rw [AddCircle.toCircle_zero, Circle.coe_one]`. Establish `hshift : ∀ (s : Af F) (q : F), s - algebraMap F (Af F) q ∈ Formalism.UG.intAd F → psiFin F s = Complex.exp (-(2 * Real.pi * Complex.I * ((trR F q : ℝ) : ℂ)))`. Introduce `s q hq`. Rewrite using `[← sub_add_cancel s (algebraMap F (Af F) q), psiFin_add, hint _ hq, one_mul, psiFin_alg]`.

Establish `hexp : ∀ t : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) = 1 ↔ ∃ n : ℤ, t = n`. Introduce `t`. Rewrite using `[Complex.exp_eq_one_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`.

Use `⟨-n, ?_⟩` and prove the remaining obligations. Establish `h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `by first`. Consider the case `exact Complex.two_pi_I_ne_zero`. Consider the case `simp [Real.pi_ne_zero]`. Establish `ht : (t : ℂ) = ((-n : ℤ) : ℂ)`.

Apply `mul_left_cancel₀ h2pi` to reduce the goal to its premises. Use `push_cast`. Take the linear combination `-hn`. Conclude with `ht` after adjusting the coercions. Introduce and unpack `⟨n, rfl⟩`.

Conclude with `⟨-n, by push_cast; ring⟩`. Prove the components needed by the constructor for the conclusion. Introduce `hall`. Apply `(hL F v x).mp` to reduce the goal to its premises. Introduce `y hy q hq`.

Establish `h` using `hall y hy`. Rewrite `h` using `[hV, hshift _ q hq, hexp]`. Take `⟨n, hn⟩` from `h`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite `hn` using `[htr]`.

Conclude with `hn` after adjusting the coercions. Introduce `hd y hy`. Rewrite using `[hV]`. Take `⟨q, hq⟩` from `fin_approx (singleV F v (x * y))`. Rewrite using `[hshift _ q hq, hexp]`.

Take `⟨n, hn⟩` from `(hL F v x).mpr hd y hy q hq`. Conclude with `⟨n, by rw [htr, hn]; norm_cast⟩`.
-/
theorem condAllTR_of (hL : LocTrDual) (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (ψ : AddChar (AF F) ℂ) (h1 : IsCharAF F ψ) (h2 : Formalism.L2.SG.LocVol.IsStdChar ψ)
    (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) :
    (∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v (x * y) = 1) ↔
      Formalism.L2.SG.LocVol.dV v * x ∈ v.adicCompletionIntegers F := by

  have htr : ∀ q : F, trR F q = ((Algebra.trace ℚ F q : ℚ) : ℝ) := by
    intro q
    have hsum : ((Algebra.trace ℚ F q : ℚ) : ℂ) = ∑ σ : F →ₐ[ℚ] ℂ, σ q := by
      have h : algebraMap ℚ ℂ (Algebra.trace ℚ F q) = ∑ σ : F →ₐ[ℚ] ℂ, σ q := by
        first
          | exact trace_eq_sum_embeddings ℂ (x := q)
          | exact trace_eq_sum_embeddings (E := ℂ) (x := q)
          | exact trace_eq_sum_embeddings ℂ q
          | exact trace_eq_sum_embeddings (L := F) ℂ
      rw [← h]
      first
        | rfl
        | (simp; done)
        | exact (eq_ratCast _ _).symm
    have hbij : Function.Bijective (fun w : InfinitePlace F => w.embedding.toRatAlgHom) := by
      constructor
      · intro w w' h
        have h' : w.embedding = w'.embedding := by
          ext z
          exact DFunLike.congr_fun h z
        rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h']
      · intro σ
        refine ⟨InfinitePlace.mk σ.toRingHom, ?_⟩
        have hr : ComplexEmbedding.IsReal (InfinitePlace.mk σ.toRingHom).embedding :=
          InfinitePlace.isReal_iff.mp (IsTotallyReal.isReal _)
        have he : (InfinitePlace.mk σ.toRingHom).embedding = σ.toRingHom := by
          rcases InfinitePlace.embedding_mk_eq σ.toRingHom with h | h
          · exact h
          · rw [h] at hr ⊢
            have h2 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ.toRingHom) =
                ComplexEmbedding.conjugate σ.toRingHom := hr
            first
              | exact ComplexEmbedding.isReal_conjugate_iff.mp hr
              | (simp only [ComplexEmbedding.conjugate, star_star] at h2; exact h2.symm)
              | (rw [star_star] at h2; exact h2.symm)
              | (have h3 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ.toRingHom) =
                    σ.toRingHom := RingHom.ext fun z => by simp [ComplexEmbedding.conjugate_coe_eq]
                 rw [h3] at h2
                 exact h2.symm)
        apply AlgHom.ext
        intro z
        show (InfinitePlace.mk σ.toRingHom).embedding z = σ z
        rw [he]
        rfl
    have hs : ∑ w : InfinitePlace F, w.embedding q = ∑ σ : F →ₐ[ℚ] ℂ, σ q :=
      Fintype.sum_bijective _ hbij _ _ (fun w => rfl)
    have hre : trR F q = (∑ w : InfinitePlace F, w.embedding q).re := by
      rw [Complex.re_sum]
      rfl
    rw [hre, hs, ← hsum]
    first
      | simp
      | exact Complex.ratCast_re _
  have hψ : ∀ z, ψ z = psiStd F z := fun z => eq_psiStd ψ h1 h2 z
  have hV : ∀ y : Fv F v, psiV F ψ v y = psiFin F (singleV F v y) := by
    intro y
    show ψ (pairA F 0 (singleV F v y)) = _
    rw [hψ]
    show psiA F 0 * psiFin F (singleV F v y) = _
    rw [psiA_zero, one_mul]
  have hint : ∀ c ∈ Formalism.UG.intAd F, psiFin F c = 1 := by
    intro c hc
    show ((AddCircle.toCircle (-((exists_psiF F).choose c)) : Circle) : ℂ) = 1
    rw [(exists_psiF F).choose_spec.1 c hc, neg_zero]
    first
      | simp
      | rw [AddCircle.toCircle_zero, Circle.coe_one]
  have hshift : ∀ (s : Af F) (q : F), s - algebraMap F (Af F) q ∈ Formalism.UG.intAd F →
      psiFin F s = Complex.exp (-(2 * Real.pi * Complex.I * ((trR F q : ℝ) : ℂ))) := by
    intro s q hq
    rw [← sub_add_cancel s (algebraMap F (Af F) q), psiFin_add, hint _ hq, one_mul, psiFin_alg]
  have hexp : ∀ t : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) = 1 ↔ ∃ n : ℤ, t = n := by
    intro t
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        first
          | exact Complex.two_pi_I_ne_zero
          | simp [Real.pi_ne_zero]
      have ht : (t : ℂ) = ((-n : ℤ) : ℂ) := by
        apply mul_left_cancel₀ h2pi
        push_cast
        linear_combination -hn
      exact_mod_cast ht
    · rintro ⟨n, rfl⟩
      exact ⟨-n, by push_cast; ring⟩
  constructor
  · intro hall
    apply (hL F v x).mp
    intro y hy q hq
    have h := hall y hy
    rw [hV, hshift _ q hq, hexp] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    rw [htr] at hn
    exact_mod_cast hn
  · intro hd y hy
    rw [hV]
    obtain ⟨q, hq⟩ := fin_approx (singleV F v (x * y))
    rw [hshift _ q hq, hexp]
    obtain ⟨n, hn⟩ := (hL F v x).mpr hd y hy q hq
    exact ⟨n, by rw [htr, hn]; norm_cast⟩

end Formalism.L2.SG.Pf.CondStd
