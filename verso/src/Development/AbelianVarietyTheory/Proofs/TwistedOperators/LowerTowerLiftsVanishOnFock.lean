import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantPairingSmallerFockDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantOne

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowerMembersRule

section Local

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin)
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.Chain.RealIt.LocalFromCover

/- English proof (translation)
Substitute `h1 h2` using the available equality. Use `⟨List.nodup_iff_injective_get.2 fun i j hij => ?_, List.nodup_iff_injective_get.2 fun i j hij => ?_⟩` and prove the remaining obligations. Use `@h.1 (.inl i) (.inl j) (by simpa [ofBlocks, List.getD_eq_getElem] using hij)` as an intermediate fact. Simplify using `using this`. Use `@h.1 (.inr i) (.inr j) (by simpa [ofBlocks, List.getD_eq_getElem] using hij)` as an intermediate fact.

Simplify using `using this`.
-/
theorem nodup_of_isParam {p q : ℕ} {l₁ l₂ : List ℚ} (h1 : l₁.length = p) (h2 : l₂.length = q)
    (h : IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ)) : l₁.Nodup ∧ l₂.Nodup := by
  subst h1 h2
  refine ⟨List.nodup_iff_injective_get.2 fun i j hij => ?_, List.nodup_iff_injective_get.2 fun i j hij => ?_⟩
  · have := @h.1 (.inl i) (.inl j) (by simpa [ofBlocks, List.getD_eq_getElem] using hij)
    simpa using this
  · have := @h.1 (.inr i) (.inr j) (by simpa [ofBlocks, List.getD_eq_getElem] using hij)
    simpa using this

/- English proof (translation)
Introduce `X p q r s lam' hadm hlow i hi hip hiq D V W S' M' τ ε e e' m' aS U' a' b he he' hm' h₂ ha hb`. Take `⟨κ, hκ⟩` from `GlobalTheory.T.exists_fockPolynomialIso_unitaryPair _ _ _ _ _ _ ε (M'.ε τ) e e' he he'`. Establish `hmC' : (m' : ℂ) = 2 * (aS : ℂ)` using `by exact_mod_cast hm'`. Establish `hmem : ∀ v, U'.symm ((X.ds r s lam').ι v) ∈ kFin M' τ` using `fun v => (h₂.kfin _).2 ⟨v, (U'.apply_symm_apply _).symm⟩`. Set `j : (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] kFin M' τ` to `{ toFun := fun v => ⟨U'.symm ((X.ds r s lam').ι v), hmem v⟩ map_add' := fun v w => Subtype.ext (by simp) map_smul' := fun c v => Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ]) }`.

Establish `hj : ∀ v, U' (j v : M'.H τ) = (X.ds r s lam').ι v` using `fun v => U'.apply_symm_apply _`. Establish `hsurj : Function.Surjective j` using `fun y => by`. Take `⟨v, hv⟩` from `(h₂.kfin y).1 y.2`. Conclude with `⟨v, Subtype.ext (U'.injective (by rw [hj, hv]))⟩`. Set `B' : Pol _ _ _ _ →ₗ[ℂ] (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] ℂ` to `{ toFun := fun P => (b (κ.symm P)).comp j map_add' := fun P Q => by ext v; simp map_smul' := fun c P => by ext v; simp }`.

Establish `hB' : ∀ P v, B' (κ P) v = b P (j v)` using `fun P v => by simp [B']`. Establish `h0 : B' = 0` using `GlobalTheory.T.no_invariant_pairing_smaller_fock_discreteSeries X p q r s lam' hadm hlow i hi hip hiq B' (fun Y hY P y => by`. Take `⟨P, rfl⟩` from `κ.surjective P`. Establish `hY' : toFrame M' τ (plainMat e' Y) ∈ lieAt W τ` using `h₂.lie ▸ ⟨Y, hY, rfl⟩`. Establish `h4 : (plainMat e' Y).trace = Y.trace` using `trace_reindex' e' Y`.

Establish `h6 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j ((X.ds r s lam').HK.act Y y) - ((aS : ℂ) * Y.trace) • j y`. Establish `h7 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j ((X.ds r s lam').HK.act Y y + ((m' : ℂ) / 2 * Y.trace) • y)`. Use `Subtype.ext (U'.injective ?_)` and prove the remaining obligations. Rewrite using `[hj, ← h₂.der Y hY y _ (hj y), dRep, (ha.der _ hY' (j y)).deriv]`. Rewrite using `[h7, map_add, LinearMap.map_smulₛₗ, map_mul, map_div₀, map_intCast, map_ofNat, trace_conj hY, hmC', sub_eq_add_neg, ← neg_smul]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `hb _ hY' P (j y)`. Rewrite `h` using `[h6, fr_toFrame, trace_toFrame, h4]`. Rewrite using `[← hκ.2, hB', hB', ← h]`.

Simplify using `[plainMat])`. Use `LinearMap.ext fun P => LinearMap.ext fun z => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩` from `hsurj z`. Rewrite using `[← hB', h0]`. Both sides reduce to the same expression.
-/
theorem pairing_eq_zero : ∀ (X : ProvA) (p q r s : ℕ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds r s lam').HK →
    GlobalTheory.PairLift.NoLow X p q lam' → ∀ i : ℕ, 1 ≤ i → i ≤ p → i ≤ q →
    ∀ (D : D7) (V W : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W S') (τ : D.what₂.Tau) (ε : Fin V.rank → Bool)
    (e : Ix (p - i) (q - i) ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m' : ℤ) (aS : ℚ)
    (U' : M'.H τ ≃ₗᵢ⋆[ℂ] (X.ds r s lam').U.H) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ))
    (b : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] ℂ), SignCompat ε e → SignCompat (M'.ε τ) e' → (m' : ℚ) = 2 * aS →
    Matches (X.ds r s lam') M' τ (plainMat e') m' U' → GlobalTheory.Chain.IoLift.IsKAct M' τ a' →
    (∀ Y ∈ lieAt W τ, ∀ P y, b (locT ε (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P + ((aS : ℂ) * Y.trace) • P) y +
      b P (a' Y y) = 0) → b = 0 := by
  intro X p q r s lam' hadm hlow i hi hip hiq D V W S' M' τ ε e e' m' aS U' a' b he he' hm' h₂ ha hb
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_fockPolynomialIso_unitaryPair _ _ _ _ _ _ ε (M'.ε τ) e e' he he'
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  have hmem : ∀ v, U'.symm ((X.ds r s lam').ι v) ∈ kFin M' τ := fun v =>
    (h₂.kfin _).2 ⟨v, (U'.apply_symm_apply _).symm⟩
  let j : (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] kFin M' τ :=
    { toFun := fun v => ⟨U'.symm ((X.ds r s lam').ι v), hmem v⟩
      map_add' := fun v w => Subtype.ext (by simp)
      map_smul' := fun c v => Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ]) }
  have hj : ∀ v, U' (j v : M'.H τ) = (X.ds r s lam').ι v := fun v => U'.apply_symm_apply _
  have hsurj : Function.Surjective j := fun y => by
    obtain ⟨v, hv⟩ := (h₂.kfin y).1 y.2
    exact ⟨v, Subtype.ext (U'.injective (by rw [hj, hv]))⟩
  let B' : Pol _ _ _ _ →ₗ[ℂ] (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] ℂ :=
    { toFun := fun P => (b (κ.symm P)).comp j
      map_add' := fun P Q => by ext v; simp
      map_smul' := fun c P => by ext v; simp }
  have hB' : ∀ P v, B' (κ P) v = b P (j v) := fun P v => by simp [B']
  have h0 : B' = 0 := GlobalTheory.T.no_invariant_pairing_smaller_fock_discreteSeries X p q r s lam' hadm hlow i hi hip hiq B' (fun Y hY P y => by
    obtain ⟨P, rfl⟩ := κ.surjective P
    have hY' : toFrame M' τ (plainMat e' Y) ∈ lieAt W τ := h₂.lie ▸ ⟨Y, hY, rfl⟩
    have h4 : (plainMat e' Y).trace = Y.trace := trace_reindex' e' Y
    have h6 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j ((X.ds r s lam').HK.act Y y) -
        ((aS : ℂ) * Y.trace) • j y := by
      have h7 : a' (toFrame M' τ (plainMat e' Y)) (j y) =
          j ((X.ds r s lam').HK.act Y y + ((m' : ℂ) / 2 * Y.trace) • y) := by
        refine Subtype.ext (U'.injective ?_)
        rw [hj, ← h₂.der Y hY y _ (hj y), dRep, (ha.der _ hY' (j y)).deriv]
      rw [h7, map_add, LinearMap.map_smulₛₗ, map_mul, map_div₀, map_intCast, map_ofNat, trace_conj hY, hmC',
        sub_eq_add_neg, ← neg_smul]
      congr 2
      ring
    have h := hb _ hY' P (j y)
    rw [h6, fr_toFrame, trace_toFrame, h4] at h
    rw [← hκ.2, hB', hB', ← h]
    simp [plainMat])
  refine LinearMap.ext fun P => LinearMap.ext fun z => ?_
  obtain ⟨v, rfl⟩ := hsurj z
  rw [← hB', h0]
  rfl

end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.ChainFr GlobalTheory.Chain.IoLift GlobalTheory.Chain.IoLift.FockOrbit GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec maxCpt)
open GlobalTheory.LowerMembers (frame_fock_orbit signCard_signed ptF_zero)
open scoped TensorProduct InnerProductSpace

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D X hIn`. Establish `hTB` using `hIn.bridge.2`. Introduce `S S' aS aT hP i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v A f₀ hf P`. Take `⟨χS, χT, hW, hexp⟩` from `hω`. Distinguish the cases in `f0 : f₀ = 0`.

Substitute `f0` using the available equality. Use function extensionality and compare the values at `g`. Simplify using `[Lift.liftInt, thetaKO, ptF_zero]`. Establish `tgt : ∀ τ, ∃ a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ), kFin M' τ ≤ M'.sm τ ∧ IsKAct M' τ a'` using `fun τ => by`. Take `⟨p, q, r, s, l₁, l₂, l₁', l₂', -, -, h3, h4, hR, -, e2⟩` from `hP τ`.

Take `⟨⟨e', he'⟩, m', hm', hU'⟩` from `hTB X W S' M' τ r s l₁' l₂' (aS τ) ⟨hR.pos', h3, h4, hR.par', hIn.chosen _ _ _ hR.par', e2⟩`. Take `⟨U', hU'⟩` from `hU' e' he'`. Take `⟨hsm, a', ha'⟩` from `GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D W _ M' τ _ _ _ _ _ _ _ hU'`. Conclude with `⟨a', hsm, ha'⟩`. Use `choose a' hsm ha' using tgt`.

Establish `h' : KSm M'` using `hsm`. Establish `hMF : IsMultMap θ M' ∅ 1 (PiTensorProduct.lift.symm F)` using `(GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hF)`. Establish `hM : ∀ F' : MultT θ M' ∅ 1, IsMultMap θ M' ∅ 1 (PiTensorProduct.lift.symm (F' : SmT M' →ₗ[ℂ] (GA D W → ℂ)))` using `fun F' => (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 F'.2)`. Set `pt : PolF D W.rank V'.rank →ₗ[ℂ] (WO V' W → ℂ)` to `pureTensorO ψ θ V' W A.cart (Fr.ofModel M').cart A.onb (Fr.ofModel M').onb f₀`. Establish `hp : ptF ψ θ A (Fr.ofModel M') f₀ = pt` using `rfl`.

Establish `hpt : ∀ φ, IsThetaFunO ψ V' W (pt φ)` using `fun φ => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW.std hθ _ _ _ _ hf.1 φ`. Establish `L` using `hIn.laws V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕`. Establish `hint : ∀ F' : MultT θ M' ∅ 1, ∀ φ x g, IntegrableOn (fun h => thetaKO ω' g h (pt φ) * (F' : SmT M' →ₗ[ℂ] (GA D W → ℂ)) x h) 𝓕 ν` using `fun F' φ x g => by`. Proceed by induction on `x using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r w`.

Use `(L.integ _ _ (hpt φ) ⟨(hM F').aut w, (hM F').cusp w⟩ g 1).const_mul r` as an intermediate fact. Use `this.congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm, rTr, mul_one]`. Both sides reduce to the same expression.

Consider the case `add x y hx hy => simp only [map_add, Pi.add_apply, mul_add]`. Conclude with `hx.add hy`. Take `⟨B, hB⟩` from `exists_trilinear ν 𝓕 (fun g h => LinearMap.proj 0 ∘ₗ ω' (g, h)) pt (MultT θ M' ∅ 1) hint`. Set `G : PolF D W.rank V'.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (GA D V' → ℂ)` to `B.compr₂ (LinearMap.applyₗ (⟨F, hF⟩ : MultT θ M' ∅ 1))`. Establish `hG : ∀ φ x, G φ x = GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω' ν 𝓕 (pt φ) (F x)` using `fun φ x => hB φ x ⟨F, hF⟩`.

Establish `hcl : ∀ w : M'.Vec, IsAutFunSm θ W (F (PiTensorProduct.tprod ℂ w)) ∧ IsCuspFun W (F (PiTensorProduct.tprod ℂ w))` using `fun w => ⟨hMF.aut w, hMF.cusp w⟩`. Establish `hT : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω' (1, oneP θ W τ Y t) (pt φ) z) (pt (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((aS τ : ℂ) * Y.trace) • φ) z) 0` using `fun τ Y hY φ z => (hIn.lie V' W A (Fr.ofModel M') θ ψ χS χT ω' f₀ τ (aS τ) (aT τ) hθ hW (hexp τ).1 (hexp τ).2 hf).2 Y hY φ z`. Establish `hBt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ (w : M'.Vec) (u : M'.sm τ), (u : M'.H τ) = dRep (M'.rep τ) Y (w τ) → G (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((aS τ : ℂ) * Y.trace) • φ) (PiTensorProduct.tprod ℂ w) + G φ (PiTensorProduct.tprod ℂ (Function.update w τ u)) = 0`. Introduce `τ Y hY φ w u hu`. Establish `e1` using `GlobalTheory.MultGelf.rder_apply hMF τ w hY (w τ) u hu`.

Rewrite `e1` using `[Function.update_eq_self]`. Establish `e2 : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT θ ω' τ Y (pt φ) = pt (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((aS τ : ℂ) * Y.trace) • φ)`. Use function extensionality and compare the values at `fun z => (hT τ Y hY φ z).deriv`. Use function extensionality and compare the values at `g`. Use `L.derT_add (hpt φ) (hcl w) τ hY g` as an intermediate fact.

Rewrite `this` using `[e2, add_comm]`. Rewrite using `[Pi.add_apply, hG, hG]`. Conclude with `(congrArg (fun A => _ + GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω' ν 𝓕 (pt φ) A g) e1).symm.trans this`. Establish `hav` using `mem_span_of_average G h' fun τ φ w => by`. Take `⟨n, φs, c, hc, hφ⟩` from `frame_fock_orbit D V' W _ A M' θ ψ ω' f₀ τ (aS τ) (aT τ) hθ (hIn.cpt V' W A (Fr.ofModel M') θ ψ χS χT ω' f₀ τ _ _ hθ hW (hexp τ).1 (hexp τ).2 hf f0) φ`.

Establish `hk` using `GlobalTheory.Chain.IoLift.kMean_mem_kFin_of_coefFam D W _ M' τ n c hc (w τ)`. Use `⟨n, φs, fun i => ⟨_, h' τ (hk i)⟩, hk, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Simplify using `only [hG, Finset.sum_apply]`. Conclude with `GlobalTheory.Chain.IoLift.AvgLift.liftInt_eq_sum_average D V' W _ M' θ ψ χS χT ω' ν 𝓕 hθ hW hν h𝓕 τ n c _ _ _ _ hc.1 (hpt φ) hφ (hcl w).1.toIsAutFun (fun i x => apply_kMean hMF τ (hc.1 i) w _ rfl x) g (hint ⟨F, hF⟩ _ _ g) fun i => hint ⟨F, hF⟩ _ _ g`.

Take `⟨τ₀⟩ : Nonempty D.what₂.Tau` from `⟨D.eTau.symm 1⟩`. Take `⟨p, q, r, s, l₁, l₂, l₁', l₂', h1, h2, h3, h4, hR, e1, e2⟩` from `hP τ₀`. Take `⟨p', q', hp', hq', hsig⟩` from `hs τ₀`. Take `⟨hn1, hn2⟩` from `nodup_of_isParam h1 h2 hR.par`. Establish `hcard` using `signCard_signed l₁ l₂ (aT τ₀) hn1 hn2`.

Rewrite `hp'` using `[e1, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard_dualPar, hcard.1, h1]`. Rewrite `hq'` using `[e1, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard_dualPar, hcard.2, h2]`. Take `rfl : p' = p - i` from `by omega`. Take `rfl : q' = q - i` from `by omega`. Take `⟨e, he⟩` from `(GlobalTheory.FrameExists.frame_exists_signCompat D V').2 A τ₀ _ _ hsig`.

Take `⟨⟨e', he'⟩, m', hm', hU'⟩` from `hTB X W S' M' τ₀ r s l₁' l₂' (aS τ₀) ⟨hR.pos', h3, h4, hR.par', hIn.chosen _ _ _ hR.par', e2⟩`. Take `⟨U', hU'⟩` from `hU' e' he'`. Establish `hadm : Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds r s (ofBlocks l₁' l₂')).HK` using `(((hIn.hc.admQ5_of_harishChandraModules X _ _ hR.pos').1 (X.ds r s (ofBlocks l₁' l₂')).U ⟨(X.ds _ _ _).nontriv, (X.ds _ _ _).irred⟩).2.2 _ (X.ds _ _ _).ι ⟨(X.ds _ _ _).ι_inj, (X.ds _ _ _).ι_range, (X.ds _ _ _).der⟩).1`. Establish `kvan : ∀ φ (y : KT M'), G φ (inclK h' y) = 0`. Establish `hz` using `span_multi (G.compl₂ (inclK h')) fun p y => by`.

Use function extensionality and compare the values at `g`. Set `b` to `slice (multi ((G.compl₂ (inclK h')).compr₂ (LinearMap.proj g))) τ₀ p y`. Establish `hb0` using `pairing_eq_zero X _ _ r s (ofBlocks l₁' l₂') hadm hR.low i hi (by omega) (by omega) D V' W _ M' τ₀ (A.ε τ₀) e e' m' (aS τ₀) U' (a' τ₀) b he he' hm' hU' (ha' τ₀) (fun Y hY Q z => by`. Simplify using `only [b, slice_apply, multi_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.proj_apply]`. Establish `eq1 : glue (Function.update p τ₀ (locT (A.ε τ₀) (M'.ε τ₀) (M'.fr τ₀ * Y * (M'.fr τ₀)⁻¹) Q + ((aS τ₀ : ℂ) * Y.trace) • Q)) = fockT τ₀ (A.ε τ₀) (M'.ε τ₀) (M'.fr τ₀ * Y * (M'.fr τ₀)⁻¹) (glue (Function.update p τ₀ Q)) + ((aS τ₀ : ℂ) * Y.trace) • glue (Function.update p τ₀ Q)`.

Rewrite using `[((GlobalTheory.T.gluing_law_holds D V'.rank W.rank).2 τ₀ _ _ _).2, Function.update_idem, Function.update_self]`. Simplify using `only [← glueM_apply, MultilinearMap.map_update_add, MultilinearMap.map_update_smul]`. Establish `eq2 : Function.update y τ₀ (a' τ₀ Y z) = Function.update (Function.update y τ₀ z) τ₀ (a' τ₀ Y (Function.update y τ₀ z τ₀))`. Rewrite using `[Function.update_idem, Function.update_self]`. Rewrite using `[eq1, eq2, inclK_tprod h' (Function.update y τ₀ z), inclK_update h' (Function.update y τ₀ z) τ₀]`.

Use `congrFun (hBt τ₀ Y hY _ _ _ ?_) g` and prove the remaining obligations. Conclude with `((ha' τ₀).der Y hY _).deriv.symm)`. Use `LinearMap.congr_fun₂ hb0 (p τ₀) (y τ₀)` as an intermediate fact. Simplify `this` using `[b, slice_apply, multi_apply, Function.update_eq_self]`. Conclude with `fun φ y => LinearMap.congr_fun₂ hz φ y`.

Establish `h0 : G P v ∈ (⊥ : Submodule ℂ (GA D V' → ℂ))` using `Submodule.span_le.2 (by rintro _ ⟨φ, y, rfl⟩; simp [kvan φ y]) (hav P v)`. Rewrite `h0` using `[Submodule.mem_bot, hG]`. Rewrite using `[hp]`. Conclude with `h0`.
-/
theorem lowFock : ∀ (D : D7) (X : ProvA), GlobalTheory.PairLift.Inputs D X → GlobalTheory.PairLift.LowFock D X := by
  classical
  intro D X hIn
  have hTB := hIn.bridge.2
  intro S S' aS aT hP i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v A f₀ hf P
  obtain ⟨χS, χT, hW, hexp⟩ := hω
  by_cases f0 : f₀ = 0
  · subst f0
    funext g
    simp [Lift.liftInt, thetaKO, ptF_zero]

  have tgt : ∀ τ, ∃ a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ),
      kFin M' τ ≤ M'.sm τ ∧ IsKAct M' τ a' := fun τ => by
    obtain ⟨p, q, r, s, l₁, l₂, l₁', l₂', -, -, h3, h4, hR, -, e2⟩ := hP τ
    obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hTB X W S' M' τ r s l₁' l₂' (aS τ)
      ⟨hR.pos', h3, h4, hR.par', hIn.chosen _ _ _ hR.par', e2⟩
    obtain ⟨U', hU'⟩ := hU' e' he'
    obtain ⟨hsm, a', ha'⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D W _ M' τ _ _ _ _ _ _ _ hU'
    exact ⟨a', hsm, ha'⟩
  choose a' hsm ha' using tgt
  have h' : KSm M' := hsm
  have hMF : IsMultMap θ M' ∅ 1 (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hF)
  have hM : ∀ F' : MultT θ M' ∅ 1, IsMultMap θ M' ∅ 1 (PiTensorProduct.lift.symm (F' : SmT M' →ₗ[ℂ] (GA D W → ℂ))) :=
    fun F' => (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 F'.2)
  let pt : PolF D W.rank V'.rank →ₗ[ℂ] (WO V' W → ℂ) :=
    pureTensorO ψ θ V' W A.cart (Fr.ofModel M').cart A.onb (Fr.ofModel M').onb f₀
  have hp : ptF ψ θ A (Fr.ofModel M') f₀ = pt := rfl
  have hpt : ∀ φ, IsThetaFunO ψ V' W (pt φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW.std hθ _ _ _ _ hf.1 φ
  have L := hIn.laws V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hint : ∀ F' : MultT θ M' ∅ 1, ∀ φ x g, IntegrableOn
      (fun h => thetaKO ω' g h (pt φ) * (F' : SmT M' →ₗ[ℂ] (GA D W → ℂ)) x h) 𝓕 ν := fun F' φ x g => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r w =>
      have := (L.integ _ _ (hpt φ) ⟨(hM F').aut w, (hM F').cusp w⟩ g 1).const_mul r
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm, rTr, mul_one]
      rfl
    | add x y hx hy => simp only [map_add, Pi.add_apply, mul_add]; exact hx.add hy
  obtain ⟨B, hB⟩ := exists_trilinear ν 𝓕 (fun g h => LinearMap.proj 0 ∘ₗ ω' (g, h)) pt (MultT θ M' ∅ 1) hint
  let G : PolF D W.rank V'.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (GA D V' → ℂ) :=
    B.compr₂ (LinearMap.applyₗ (⟨F, hF⟩ : MultT θ M' ∅ 1))
  have hG : ∀ φ x, G φ x = GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω' ν 𝓕 (pt φ) (F x) := fun φ x => hB φ x ⟨F, hF⟩
  have hcl : ∀ w : M'.Vec, IsAutFunSm θ W (F (PiTensorProduct.tprod ℂ w)) ∧
      IsCuspFun W (F (PiTensorProduct.tprod ℂ w)) := fun w => ⟨hMF.aut w, hMF.cusp w⟩

  have hT : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω' (1, oneP θ W τ Y t) (pt φ) z)
      (pt (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((aS τ : ℂ) * Y.trace) • φ) z) 0 :=
    fun τ Y hY φ z => (hIn.lie V' W A (Fr.ofModel M') θ ψ χS χT ω' f₀ τ (aS τ) (aT τ) hθ hW
      (hexp τ).1 (hexp τ).2 hf).2 Y hY φ z
  have hBt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ (w : M'.Vec) (u : M'.sm τ), (u : M'.H τ) = dRep (M'.rep τ) Y (w τ) →
      G (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((aS τ : ℂ) * Y.trace) • φ)
        (PiTensorProduct.tprod ℂ w) + G φ (PiTensorProduct.tprod ℂ (Function.update w τ u)) = 0 := by
    intro τ Y hY φ w u hu
    have e1 := GlobalTheory.MultGelf.rder_apply hMF τ w hY (w τ) u hu
    rw [Function.update_eq_self] at e1
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT θ ω' τ Y (pt φ) =
        pt (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((aS τ : ℂ) * Y.trace) • φ) :=
      funext fun z => (hT τ Y hY φ z).deriv
    funext g
    have := L.derT_add (hpt φ) (hcl w) τ hY g
    rw [e2, add_comm] at this
    rw [Pi.add_apply, hG, hG]
    exact (congrArg (fun A => _ + GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω' ν 𝓕 (pt φ) A g) e1).symm.trans this

  have hav := mem_span_of_average G h' fun τ φ w => by
    obtain ⟨n, φs, c, hc, hφ⟩ := frame_fock_orbit D V' W _ A M' θ ψ ω' f₀ τ (aS τ) (aT τ) hθ
      (hIn.cpt V' W A (Fr.ofModel M') θ ψ χS χT ω' f₀ τ _ _ hθ hW (hexp τ).1 (hexp τ).2 hf f0) φ
    have hk := GlobalTheory.Chain.IoLift.kMean_mem_kFin_of_coefFam D W _ M' τ n c hc (w τ)
    refine ⟨n, φs, fun i => ⟨_, h' τ (hk i)⟩, hk, ?_⟩
    funext g
    simp only [hG, Finset.sum_apply]
    exact GlobalTheory.Chain.IoLift.AvgLift.liftInt_eq_sum_average D V' W _ M' θ ψ χS χT ω' ν 𝓕 hθ hW hν h𝓕 τ n c _ _ _ _
      hc.1 (hpt φ) hφ (hcl w).1.toIsAutFun (fun i x => apply_kMean hMF τ (hc.1 i) w _ rfl x) g
      (hint ⟨F, hF⟩ _ _ g) fun i => hint ⟨F, hF⟩ _ _ g

  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  obtain ⟨p, q, r, s, l₁, l₂, l₁', l₂', h1, h2, h3, h4, hR, e1, e2⟩ := hP τ₀
  obtain ⟨p', q', hp', hq', hsig⟩ := hs τ₀
  obtain ⟨hn1, hn2⟩ := nodup_of_isParam h1 h2 hR.par
  have hcard := signCard_signed l₁ l₂ (aT τ₀) hn1 hn2
  rw [e1, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard_dualPar, hcard.1, h1] at hp'
  rw [e1, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard_dualPar, hcard.2, h2] at hq'
  obtain rfl : p' = p - i := by omega
  obtain rfl : q' = q - i := by omega
  obtain ⟨e, he⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').2 A τ₀ _ _ hsig
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hTB X W S' M' τ₀ r s l₁' l₂' (aS τ₀)
    ⟨hR.pos', h3, h4, hR.par', hIn.chosen _ _ _ hR.par', e2⟩
  obtain ⟨U', hU'⟩ := hU' e' he'
  have hadm : Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds r s (ofBlocks l₁' l₂')).HK :=
    (((hIn.hc.admQ5_of_harishChandraModules X _ _ hR.pos').1 (X.ds r s (ofBlocks l₁' l₂')).U
      ⟨(X.ds _ _ _).nontriv, (X.ds _ _ _).irred⟩).2.2 _ (X.ds _ _ _).ι
      ⟨(X.ds _ _ _).ι_inj, (X.ds _ _ _).ι_range, (X.ds _ _ _).der⟩).1
  have kvan : ∀ φ (y : KT M'), G φ (inclK h' y) = 0 := by
    have hz := span_multi (G.compl₂ (inclK h')) fun p y => by
      funext g
      let b := slice (multi ((G.compl₂ (inclK h')).compr₂ (LinearMap.proj g))) τ₀ p y
      have hb0 := pairing_eq_zero X _ _ r s (ofBlocks l₁' l₂') hadm hR.low i hi (by omega) (by omega) D V' W _ M' τ₀
        (A.ε τ₀) e e' m' (aS τ₀) U' (a' τ₀) b he he' hm' hU' (ha' τ₀) (fun Y hY Q z => by
          simp only [b, slice_apply, multi_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
            LinearMap.proj_apply]
          have eq1 : glue (Function.update p τ₀ (locT (A.ε τ₀) (M'.ε τ₀) (M'.fr τ₀ * Y * (M'.fr τ₀)⁻¹) Q +
              ((aS τ₀ : ℂ) * Y.trace) • Q)) =
              fockT τ₀ (A.ε τ₀) (M'.ε τ₀) (M'.fr τ₀ * Y * (M'.fr τ₀)⁻¹) (glue (Function.update p τ₀ Q)) +
                ((aS τ₀ : ℂ) * Y.trace) • glue (Function.update p τ₀ Q) := by
            rw [((GlobalTheory.T.gluing_law_holds D V'.rank W.rank).2 τ₀ _ _ _).2, Function.update_idem, Function.update_self]
            simp only [← glueM_apply, MultilinearMap.map_update_add, MultilinearMap.map_update_smul]
          have eq2 : Function.update y τ₀ (a' τ₀ Y z) = Function.update (Function.update y τ₀ z) τ₀
              (a' τ₀ Y (Function.update y τ₀ z τ₀)) := by
            rw [Function.update_idem, Function.update_self]
          rw [eq1, eq2, inclK_tprod h' (Function.update y τ₀ z), inclK_update h' (Function.update y τ₀ z) τ₀]
          refine congrFun (hBt τ₀ Y hY _ _ _ ?_) g
          exact ((ha' τ₀).der Y hY _).deriv.symm)
      have := LinearMap.congr_fun₂ hb0 (p τ₀) (y τ₀)
      simpa [b, slice_apply, multi_apply, Function.update_eq_self] using this
    exact fun φ y => LinearMap.congr_fun₂ hz φ y
  have h0 : G P v ∈ (⊥ : Submodule ℂ (GA D V' → ℂ)) :=
    Submodule.span_le.2 (by rintro _ ⟨φ, y, rfl⟩; simp [kvan φ y]) (hav P v)
  rw [Submodule.mem_bot, hG] at h0
  rw [hp]
  exact h0

end Global

end GlobalTheory.LowerMembersRule

end
