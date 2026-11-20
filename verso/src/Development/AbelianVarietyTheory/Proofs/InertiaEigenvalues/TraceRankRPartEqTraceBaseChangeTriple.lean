import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.TripleTrace

open GlobalTheory.BlockComplement

/- English proof (translation)
Establish `hl` using `GlobalTheory.TwistedSelmerCompare.natCast_mem_maximalIdeal (l := D.nd.l a) (D.nd.O a)`. Establish `hl0 : ((D.nd.l a : ℕ) : D.ntw.O0 (D.ntw.twOf a)) ≠ 0`. Introduce `h0`. Use `congrArg ((iotaOQ D.nd D.naut a).comp (D.ntw.twist₂ a)) h0` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero]`.

Conclude with `(D.nd.lPrime a).out.ne_zero (by exact_mod_cast this)`. Establish `hp : ((IsLocalRing.maximalIdeal (D.nd.O a)).comap (D.ntw.twist₂ a)).IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hm : ((IsLocalRing.maximalIdeal (D.nd.O a)).comap (D.ntw.twist₂ a)).IsMaximal` using `hp.isMaximal fun h => by`. Apply `hl0` to reduce the goal to its premises. Rewrite using `[← Ideal.mem_bot, ← h, Ideal.mem_comap, map_natCast]`.

Conclude with `hl`. Establish `he` using `IsLocalRing.eq_maximalIdeal hm`. Use `continuous_of_continuousAt_zero (D.ntw.twist₂ a) ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero, (D.ntw.twistBaseCoefficientRing_isAdic _).hasBasis_nhds_zero.tendsto_iff (D.nd.O_adic a).hasBasis_nhds_zero]`. Use `fun n _ => ⟨n, trivial, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite `hx` using `[← he]`. Conclude with `Ideal.le_comap_pow _ n hx`.
-/
theorem continuous_twO (D : D7) (a : D.nd.Loc) : Continuous (D.ntw.twist₂ a) := by
  have hl := GlobalTheory.TwistedSelmerCompare.natCast_mem_maximalIdeal (l := D.nd.l a) (D.nd.O a)
  have hl0 : ((D.nd.l a : ℕ) : D.ntw.O0 (D.ntw.twOf a)) ≠ 0 := by
    intro h0
    have := congrArg ((iotaOQ D.nd D.naut a).comp (D.ntw.twist₂ a)) h0
    rw [map_natCast, map_zero] at this
    exact (D.nd.lPrime a).out.ne_zero (by exact_mod_cast this)
  have hp : ((IsLocalRing.maximalIdeal (D.nd.O a)).comap (D.ntw.twist₂ a)).IsPrime := Ideal.comap_isPrime _ _
  have hm : ((IsLocalRing.maximalIdeal (D.nd.O a)).comap (D.ntw.twist₂ a)).IsMaximal := hp.isMaximal fun h => by
    apply hl0
    rw [← Ideal.mem_bot, ← h, Ideal.mem_comap, map_natCast]
    exact hl
  have he := IsLocalRing.eq_maximalIdeal hm
  refine continuous_of_continuousAt_zero (D.ntw.twist₂ a) ?_
  rw [ContinuousAt, map_zero,
    (D.ntw.twistBaseCoefficientRing_isAdic _).hasBasis_nhds_zero.tendsto_iff (D.nd.O_adic a).hasBasis_nhds_zero]
  refine fun n _ => ⟨n, trivial, fun x hx => ?_⟩
  rw [← he] at hx
  exact Ideal.le_comap_pow _ n hx

/- English proof (translation)
Establish `e1 : e.conj (Matrix.toLin' M) = LinearMap.prodMap (Matrix.toLin' M') (Matrix.toLin' (Matrix.diagonal c))`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Take `⟨u, rfl⟩` from `e.surjective x`. Rewrite using `[LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, Matrix.toLin'_apply, h]`. Use `Prod.ext rfl ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `j`. Simplify using `[Matrix.mulVec_diagonal]`. Rewrite using `[← Matrix.trace_toLin'_eq, ← LinearMap.trace_conj' _ e, e1, LinearMap.trace_prodMap', Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Matrix.trace_diagonal]`.
-/
theorem trace_of_block {K : Type} [Field K] {n a t : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (M' : Matrix (Fin a) (Fin a) K) (c : Fin t → K) (e : (Fin n → K) ≃ₗ[K] ((Fin a → K) × (Fin t → K)))
    (h : ∀ u, e (M.mulVec u) = (M'.mulVec (e u).1, fun j => c j * (e u).2 j)) :
    M.trace = M'.trace + ∑ j, c j := by
  have e1 : e.conj (Matrix.toLin' M) =
      LinearMap.prodMap (Matrix.toLin' M') (Matrix.toLin' (Matrix.diagonal c)) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨u, rfl⟩ := e.surjective x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, Matrix.toLin'_apply, h]
    refine Prod.ext rfl ?_
    funext j
    simp [Matrix.mulVec_diagonal]
  rw [← Matrix.trace_toLin'_eq, ← LinearMap.trace_conj' _ e, e1, LinearMap.trace_prodMap',
    Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Matrix.trace_diagonal]

/- English proof (translation)
Introduce and unpack `hC D i π ρ s Sg ⟨hρ, r₀, ⟨-, -, hr3⟩, e, he⟩ ⟨P, hP, -, -, -, hB4, -⟩ ⟨-, -, -, hT⟩ g`. Establish `hι` using `GlobalTheory.CoeffEmbedding.continuous_iotaOQ _ _ _ D.nd D.naut i`. Establish `hinj : Function.Injective (iotaOQ D.nd D.naut i)` using `(D.naut.iotaQ i).injective.comp (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))`. Apply `hinj` to reduce the goal to its premises. Use `revert g`.

Rewrite using `[← funext_iff]`. Use `AE.eq_of_continuous hC (hι.comp hρ.matrix_trace) (hι.comp ((continuous_twO D i).comp (D.ntw.rhoS_cont _ s).matrix_trace)) ?_` and prove the remaining obligations. Use `filter_upwards [hT, ae_chiBar D.naut i, ae_epsBar D.naut i, eventually_out i, isoLoc_sum (A := D.naut) (twistIso D.nd D.naut (Sg ++ [muPart D.nd D.naut i]) D.naut.etaTinv), isoLoc_sum (A := D.naut) (twistIso D.nd D.naut Sg D.naut.etaTinv)] with w h1 h2 h3 h4 h5 h8 hw B σ hB hσ`. Apply `(D.naut.iotaQC i).injective` to reduce the goal to its premises. Establish `hq` using `normV_ne_zero w`.

Establish `h6` using `D.naut.pt_loc i P π hP w (h4 hw)`. Rewrite `h6` using `[← hr3 w (h4 hw) B σ hB hσ, ← hB4 w hw]`. Establish `h9` using `map_trace_eq_sum _ _ _ h6`. Establish `h10` using `map_trace_eq_sum _ _ _ (h1 (h4 hw) B σ hB hσ)`. Rewrite `h9` using `[D.naut.frobEig_tw _ _ h5.1, Multiset.sum_map_mul_right, Multiset.map_id', h5.2]`.

Rewrite `h10` using `[D.naut.frobEig_tw _ _ h8.1, Multiset.sum_map_mul_right, Multiset.map_id', h8.2]`. Establish `h7 : ∑ c : Fin D.R.t, D.naut.iotaQC i (chiBar D.naut i (c.1 + 1) σ) = sumPart D.naut ⟨1, muEta D.naut i, D.R.t⟩ w * ((normV w : ℕ) : ℂ) ^ ((((1 - (D.R.nV : ℝ)) / 2 : ℝ)) : ℂ)`. Rewrite using `[sumPart, ← List.sum_map_mul_right, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.sum_range]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[chiBar_succ c.1 c.2, map_mul, map_zpow₀, h2 hw B σ hB hσ, h3 hw B σ hB hσ, ← Complex.cpow_intCast, mul_assoc, mul_assoc, ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h11` using `congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (trace_of_block _ _ _ e (he σ))`. Establish `h12 : iotaO D.nd D.naut i ((r₀ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) _).trace = iotaO D.nd D.naut i ((ρ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).trace + ∑ c : Fin D.R.t, D.naut.iotaQC i (chiBar D.naut i (c.1 + 1) σ)`.

Simplify using `only [map_add, map_sum] at h11`. Use `Eq.trans ?_ (h11.trans ?_)` and prove the remaining obligations. Conclude with `congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (AddMonoidHom.map_trace (toK D.nd i) _)`. Use `congr 1`. Conclude with `congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (AddMonoidHom.map_trace (toK D.nd i) _).symm`.

Use `Eq.trans ?_ h10.symm` and prove the remaining obligations. Establish `h13` using `h12.symm.trans h9`. Rewrite `h13` using `[h7]`. Simplify using `only [twistIso, muPart, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero, add_mul] at h13`. Conclude with `add_right_cancel h13`.
-/
theorem trace_eq : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (a : D.nd.Loc) (π : D.nd.X a) (ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π ρ → HasParamX D.nd D.naut a π Sg → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsTriple D a s Sg → ∀ g, ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).trace = D.ntw.twist₂ a ((D.ntw.rhoS _ s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).trace := by
  rintro hC D i π ρ s Sg ⟨hρ, r₀, ⟨-, -, hr3⟩, e, he⟩ ⟨P, hP, -, -, -, hB4, -⟩ ⟨-, -, -, hT⟩ g
  have hι := GlobalTheory.CoeffEmbedding.continuous_iotaOQ _ _ _ D.nd D.naut i
  have hinj : Function.Injective (iotaOQ D.nd D.naut i) :=
    (D.naut.iotaQ i).injective.comp (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
  apply hinj
  revert g
  rw [← funext_iff]
  refine AE.eq_of_continuous hC (hι.comp hρ.matrix_trace)
    (hι.comp ((continuous_twO D i).comp (D.ntw.rhoS_cont _ s).matrix_trace)) ?_
  filter_upwards [hT, ae_chiBar D.naut i, ae_epsBar D.naut i, eventually_out i,
    isoLoc_sum (A := D.naut) (twistIso D.nd D.naut (Sg ++ [muPart D.nd D.naut i]) D.naut.etaTinv),
    isoLoc_sum (A := D.naut) (twistIso D.nd D.naut Sg D.naut.etaTinv)]
    with w h1 h2 h3 h4 h5 h8 hw B σ hB hσ
  apply (D.naut.iotaQC i).injective
  have hq := normV_ne_zero w
  have h6 := D.naut.pt_loc i P π hP w (h4 hw)
  rw [← hr3 w (h4 hw) B σ hB hσ, ← hB4 w hw] at h6
  have h9 := map_trace_eq_sum _ _ _ h6
  have h10 := map_trace_eq_sum _ _ _ (h1 (h4 hw) B σ hB hσ)
  rw [D.naut.frobEig_tw _ _ h5.1, Multiset.sum_map_mul_right, Multiset.map_id', h5.2] at h9
  rw [D.naut.frobEig_tw _ _ h8.1, Multiset.sum_map_mul_right, Multiset.map_id', h8.2] at h10
  have h7 : ∑ c : Fin D.R.t, D.naut.iotaQC i (chiBar D.naut i (c.1 + 1) σ) =
      sumPart D.naut ⟨1, muEta D.naut i, D.R.t⟩ w *
        ((normV w : ℕ) : ℂ) ^ ((((1 - (D.R.nV : ℝ)) / 2 : ℝ)) : ℂ) := by
    rw [sumPart, ← List.sum_map_mul_right, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
      Finset.sum_range]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [chiBar_succ c.1 c.2, map_mul, map_zpow₀, h2 hw B σ hB hσ, h3 hw B σ hB hσ, ← Complex.cpow_intCast,
      mul_assoc, mul_assoc, ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]
    congr 2
    push_cast
    ring
  have h11 := congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (trace_of_block _ _ _ e (he σ))
  have h12 : iotaO D.nd D.naut i ((r₀ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) _).trace =
      iotaO D.nd D.naut i ((ρ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).trace +
        ∑ c : Fin D.R.t, D.naut.iotaQC i (chiBar D.naut i (c.1 + 1) σ) := by
    simp only [map_add, map_sum] at h11
    refine Eq.trans ?_ (h11.trans ?_)
    · exact congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (AddMonoidHom.map_trace (toK D.nd i) _)
    · congr 1
      exact congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (AddMonoidHom.map_trace (toK D.nd i) _).symm
  refine Eq.trans ?_ h10.symm
  have h13 := h12.symm.trans h9
  rw [h7] at h13
  simp only [twistIso, muPart, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, add_zero, add_mul] at h13
  exact add_right_cancel h13

end GlobalTheory.TripleTrace

end
