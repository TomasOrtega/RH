import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BHRSmulRight

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

section DualH

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Establish `hinv` using `b_sig_sig σ hcm`. Establish `hnt` using `b_sig_nt σ hcm`. Establish `hfin : Module.finrank F E = 2` using `hcm.2.2.1`. Apply `(algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective` to reduce the goal to its premises. Rewrite using `[trace_v v σ hinv hnt hfin, trace_v v σ hinv hnt hfin, sigR_sigR v σ hinv, add_comm]`.
-/
theorem b_tr_sig (hcm : IsCMExt F E σ) (w : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sigR (Fv F v) σ w) = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w := by
  have hinv := b_sig_sig σ hcm
  have hnt := b_sig_nt σ hcm
  have hfin : Module.finrank F E = 2 := hcm.2.2.1
  apply (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective
  rw [trace_v v σ hinv hnt hfin, trace_v v σ hinv hnt hfin, sigR_sigR v σ hinv, add_comm]

def hm {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (i j : Fin a) (c : Fv F v ⊗[F] E) : HermR (Fv F v) σ a :=
  ⟨Matrix.single i j c + Matrix.single j i (sigR (Fv F v) σ c), fun p q => by
    simp only [Matrix.add_apply, Matrix.single_apply]
    rw [map_add, apply_ite (sigR (Fv F v) σ), apply_ite (sigR (Fv F v) σ), map_zero, sigR_sigR v σ hinv, add_comm]
    congr 1 <;> exact if_congr and_comm rfl rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_hm {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (i j : Fin a) (c : Fv F v ⊗[F] E) :
    (hm σ v hinv i j c : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) =
      Matrix.single i j c + Matrix.single j i (sigR (Fv F v) σ c) := rfl

/- English proof (translation)
Introduce `p q`. Rewrite using `[coe_hm, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `hc`.

Conclude with `Submodule.zero_mem _`. Use `split_ifs`. Conclude with `b_sigR_mem v σ hc`. Conclude with `Submodule.zero_mem _`.
-/
theorem hm_mem {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (i j : Fin a) {c : Fv F v ⊗[F] E}
    (hc : c ∈ OEv (E := E) v) : hm σ v hinv i j c ∈ HO σ v a := by
  intro p q
  rw [coe_hm, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
  refine Submodule.add_mem _ ?_ ?_
  · split_ifs
    · exact hc
    · exact Submodule.zero_mem _
  · split_ifs
    · exact b_sigR_mem v σ hc
    · exact Submodule.zero_mem _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sum_eq_trace {a : ℕ} (M N : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    ∑ p, ∑ q, M p q * N q p = (M * N).trace := by
  rfl

/- English proof (translation)
Rewrite using `[← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, one_div, inv_mul_cancel₀ two_ne_zero, map_one]`.
-/
theorem half_two : algebraMap F (Fv F v) (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, one_div, inv_mul_cancel₀ two_ne_zero, map_one]

/- English proof (translation)
Rewrite using `[← two_mul, ← mul_assoc, half_two, one_mul]`.
-/
theorem half_mul (t : Fv F v) : algebraMap F (Fv F v) (1 / 2) * (t + t) = t := by
  rw [← two_mul, ← mul_assoc, half_two, one_mul]

/- English proof (translation)
Unfold `pairHerm`. Rewrite using `[sum_eq_trace, coe_hm, add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul, smul_eq_mul, smul_eq_mul, ← T.2 i j, ← map_mul (sigR (Fv F v) σ), map_add, b_tr_sig σ v hcm, half_mul]`.
-/
theorem pair_hm (hcm : IsCMExt F E σ) {a : ℕ} (i j : Fin a) (c : Fv F v ⊗[F] E) (T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a (hm σ v (b_sig_sig σ hcm) i j c) T =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c * (T : Matrix (Fin a) (Fin a) _) j i) := by
  unfold pairHerm
  rw [sum_eq_trace, coe_hm, add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul,
    smul_eq_mul, smul_eq_mul, ← T.2 i j, ← map_mul (sigR (Fv F v) σ), map_add, b_tr_sig σ v hcm, half_mul]

/- English proof (translation)
Simplify using `only [pairHerm, coe_hermSMul, Matrix.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairHerm_smul_right' {a : ℕ} (s : Fv F v) (S T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a S (s • T) = s * pairHerm (Fv F v) σ a S T := by
  simp only [pairHerm, coe_hermSMul, Matrix.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul,
    smul_eq_mul]
  ring

/- English proof (translation)
Establish `hinv` using `b_sig_sig σ hcm`. Establish `hnt` using `b_sig_nt σ hcm`. Establish `hfin : Module.finrank F E = 2` using `hcm.2.2.1`. Use `set u := ∑ p, ∑ q, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q * (T : Matrix (Fin a) (Fin a) _) q p with hudef`. Establish `hu : u ∈ OEv (E` using `E) v := sum_mem fun p _ => sum_mem fun q _ => b_mul_mem v (hS p q) (hT q p)`.

Establish `hfix : sigR (Fv F v) σ u = u`. Rewrite using `[hudef, map_sum]`. Simplify using `only [map_sum, map_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Rewrite using `[← S.2 p q, ← T.2 q p]`. Establish `hsc : sc (E` using `E) v (pairHerm (Fv F v) σ a S T) = u := by`. Establish `htr : sc (E` using `E) v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) u) = u + u := by`. Rewrite using `[b_sc_eq, trace_v v σ hinv hnt hfin, hfix]`. Establish `h2 : sc (E` using `E) v (algebraMap F (Fv F v) (1 / 2)) * 2 = 1 := by`.

Establish `e2 : (2 : Fv F v ⊗[F] E) = sc (E` using `E) v 2 := by rw [b_sc_eq, map_ofNat]`. Rewrite using `[e2, b_sc_eq, b_sc_eq, ← map_mul, half_two, map_one]`. Establish `hm2 : ∀ x y : Fv F v, sc (E` using `E) v (x * y) = sc (E := E) v x * sc (E := E) v y := fun x y => by`. Simplify using `only [b_sc_eq, map_mul]`. Unfold `pairHerm`.

Rewrite using `[← hudef, hm2, htr, ← two_mul, ← mul_assoc, h2, one_mul]`. Conclude with `b_int_of_sc v (hsc ▸ hu)`.
-/
theorem pair_int (hcm : IsCMExt F E σ) {a : ℕ} {S T : HermR (Fv F v) σ a} (hS : S ∈ HO σ v a) (hT : T ∈ HO σ v a) :
    pairHerm (Fv F v) σ a S T ∈ v.adicCompletionIntegers F := by
  have hinv := b_sig_sig σ hcm
  have hnt := b_sig_nt σ hcm
  have hfin : Module.finrank F E = 2 := hcm.2.2.1
  set u := ∑ p, ∑ q, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q * (T : Matrix (Fin a) (Fin a) _) q p
    with hudef
  have hu : u ∈ OEv (E := E) v :=
    sum_mem fun p _ => sum_mem fun q _ => b_mul_mem v (hS p q) (hT q p)
  have hfix : sigR (Fv F v) σ u = u := by
    rw [hudef, map_sum]
    simp only [map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← S.2 p q, ← T.2 q p]
  have hsc : sc (E := E) v (pairHerm (Fv F v) σ a S T) = u := by
    have htr : sc (E := E) v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) u) = u + u := by
      rw [b_sc_eq, trace_v v σ hinv hnt hfin, hfix]
    have h2 : sc (E := E) v (algebraMap F (Fv F v) (1 / 2)) * 2 = 1 := by
      have e2 : (2 : Fv F v ⊗[F] E) = sc (E := E) v 2 := by rw [b_sc_eq, map_ofNat]
      rw [e2, b_sc_eq, b_sc_eq, ← map_mul, half_two, map_one]
    have hm2 : ∀ x y : Fv F v, sc (E := E) v (x * y) = sc (E := E) v x * sc (E := E) v y := fun x y => by
      simp only [b_sc_eq, map_mul]
    unfold pairHerm
    rw [← hudef, hm2, htr, ← two_mul, ← mul_assoc, h2, one_mul]
  exact b_int_of_sc v (hsc ▸ hu)

/- English proof (translation)
Introduce `hS hU`. Establish `hcm` using `hS.1`. Establish `hd0` using `dV_ne_zero v`. Use extensionality with `T`. Simplify using `only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_smulSub]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨dV v • T, fun i j => ?_, by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]⟩` and prove the remaining obligations. Rewrite using `[coe_hermSMul, Matrix.smul_apply, Algebra.smul_def]`. Use `hP hS hU _ fun c hc => ?_` and prove the remaining obligations.

Establish `h1` using `h _ (hm_mem σ v (b_sig_sig σ hcm) j i hc)`. Rewrite `h1` using `[pair_hm σ v hcm]`. Rewrite using `[mul_left_comm, ← b_sc_eq, b_tr_sc]`. Conclude with `h1`. Introduce and unpack `⟨T', hT', rfl⟩ S hS'`.

Rewrite using `[pairHerm_smul_right', ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]`. Conclude with `pair_int σ v hcm hS' hT'`.
-/
theorem dualH_of_perf (a : ℕ) (hP : TrPerf σ J ψ v) : DualH σ J ψ v a := by
  intro hS hU
  have hcm := hS.1
  have hd0 := dV_ne_zero v
  ext T
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_smulSub]
  constructor
  · intro h
    refine ⟨dV v • T, fun i j => ?_, by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]⟩
    rw [coe_hermSMul, Matrix.smul_apply, Algebra.smul_def]
    refine hP hS hU _ fun c hc => ?_
    have h1 := h _ (hm_mem σ v (b_sig_sig σ hcm) j i hc)
    rw [pair_hm σ v hcm] at h1
    rw [mul_left_comm, ← b_sc_eq, b_tr_sc]
    exact h1
  · rintro ⟨T', hT', rfl⟩ S hS'
    rw [pairHerm_smul_right', ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
    exact pair_int σ v hcm hS' hT'

end DualH

end PI.OmLocU.SdB
