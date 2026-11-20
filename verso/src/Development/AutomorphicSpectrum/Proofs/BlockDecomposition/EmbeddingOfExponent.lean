import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportOfExponentOfCasselman
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisTer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbLeviProjMemKm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityNonzero

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.GlFrob

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `k _ _ _ _ _ n hd1 V _ _ π hs ha hirr ξ hξ hd hv`. Take `⟨v, hv0, hv⟩` from `hv`. Establish `h0` using `GlobalTheory.CompanionTheory.KmIwahori.c0 k`. Establish `h3` using `GlobalTheory.CompanionTheory.Lbc.c3 k`. Establish `hcomm : ∀ l l' : Levi k (fun _ : Fin n => Fin 1), jac (stdBlocks (fun _ : Fin n => 1) hd1) π l * jac (stdBlocks (fun _ : Fin n => 1) hd1) π l' = jac (stdBlocks (fun _ : Fin n => 1) hd1) π l' * jac (stdBlocks (fun _ : Fin n => 1) hd1) π l`.

Introduce `l l'`. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `GlobalTheory.CompanionTheory.PinLift.gl_one_comm _ _`.

Take `⟨hanti, hpow⟩` from `GlobalTheory.T.deep_level_subgroups_filtration (k := k) n hd1`. Establish `hsm : ∀ w : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)), ∃ m, ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1, jac (stdBlocks (fun _ : Fin n => 1) hd1) π u w = w`. Introduce `w`. Take `⟨m, hm, h⟩` from `GlobalTheory.T.jacquet_vector_fixed_deep_level (k := k) n hd1 π hs w`. Use `⟨m - 1, ?_⟩` and prove the remaining obligations.

Rewrite using `[Nat.sub_add_cancel hm]`. Conclude with `h`. Establish `hfd : ∀ m, FiniteDimensional ℂ ↥(⨅ u : PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1, LinearMap.ker (jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) - 1))`. Introduce `m`. Use `haveI := GlobalTheory.T.jacquet_module_admissible_fixed (k := k) n hd1 π ha h0 h3 (m + 1) (by omega)`.

Use `Submodule.finiteDimensional_of_le (S₂ := fixed (jac (stdBlocks (fun _ : Fin n => 1) hd1) π) (PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1)) ?_` and prove the remaining obligations. Introduce `w hw u`. Establish `h1` using `(Submodule.mem_iInf _).1 hw u`. Establish `h2 : (jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) - 1) w = 0` using `h1`. Establish `h3' : jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) w = w`.

Simplify `h2` using `[sub_eq_zero]`. Simplify using `using h3'`. Take `⟨f, hf0, hf⟩` from `GlobalTheory.T.generalized_eigenvector_exists (Levi k (fun _ : Fin n => Fin 1)) (Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1))) (jac (stdBlocks (fun _ : Fin n => 1) hd1) π) hcomm (fun m => PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1) han …`. Take `⟨g, w, hg⟩` from `GlobalTheory.T.jacquet_cuspidal_support_of_functional n π ξ hξ hd f hf0 hf`. Take `⟨G, x, hx⟩` from `GlobalTheory.CompanionTheory.FrobInv.exists_map_prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd π hs g ⟨w, hg⟩`.

Use `⟨G, ?_⟩` and prove the remaining obligations. Establish `hso : IsSimpleOrder (Subrepresentation π)` using `hirr`. Establish `hk : ∀ y, y ∈ G.ker.toSubmodule ↔ G y = 0` using `fun y => Iff.rfl`. Break down `eq_bot_or_eq_top G.ker with h0' | h0'` into its components or cases. Use `(injective_iff_map_eq_zero G.toLinearMap).2 fun y hy => ?_` and prove the remaining obligations.

Establish `hy' : y ∈ G.ker.toSubmodule` using `(hk y).2 hy`. Rewrite `hy'` using `[h0']`. Conclude with `(Submodule.mem_bot ℂ).1 hy'`. Use `absurd ((hk x).1 ?_) hx` and prove the remaining obligations. Rewrite using `[h0']`.

Discharge the goal by the elementary cases of `trivial`.
-/
theorem embedding_of_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (hd1 : ∑ _a : Fin n, 1 = n) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsAdmissible π → π.IsIrreducible → ∀ (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ a, IsSmoothChar (ξ a)) (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n), (∃ v : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)), v ≠ 0 ∧ ∀ t : Levi k (fun _ : Fin n => Fin 1), v ∈ Module.End.maxGenEigenspace (jac (stdBlocks (fun _ : Fin n => 1) hd1) π t) (PositivityTheory.Lbc.torusChar ξ t)) → ∃ f : π.IntertwiningMap (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd), Function.Injective f := by
  intro k _ _ _ _ _ n hd1 V _ _ π hs ha hirr ξ hξ hd hv
  obtain ⟨v, hv0, hv⟩ := hv
  have h0 := GlobalTheory.CompanionTheory.KmIwahori.c0 k
  have h3 := GlobalTheory.CompanionTheory.Lbc.c3 k
  have hcomm : ∀ l l' : Levi k (fun _ : Fin n => Fin 1),
      jac (stdBlocks (fun _ : Fin n => 1) hd1) π l * jac (stdBlocks (fun _ : Fin n => 1) hd1) π l' =
        jac (stdBlocks (fun _ : Fin n => 1) hd1) π l' * jac (stdBlocks (fun _ : Fin n => 1) hd1) π l := by
    intro l l'
    rw [← map_mul, ← map_mul]
    congr 1
    funext a
    exact GlobalTheory.CompanionTheory.PinLift.gl_one_comm _ _
  obtain ⟨hanti, hpow⟩ := GlobalTheory.T.deep_level_subgroups_filtration (k := k) n hd1
  have hsm : ∀ w : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)), ∃ m,
      ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1,
        jac (stdBlocks (fun _ : Fin n => 1) hd1) π u w = w := by
    intro w
    obtain ⟨m, hm, h⟩ := GlobalTheory.T.jacquet_vector_fixed_deep_level (k := k) n hd1 π hs w
    refine ⟨m - 1, ?_⟩
    rw [Nat.sub_add_cancel hm]
    exact h
  have hfd : ∀ m, FiniteDimensional ℂ ↥(⨅ u : PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1,
      LinearMap.ker (jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) - 1)) := by
    intro m
    haveI := GlobalTheory.T.jacquet_module_admissible_fixed (k := k) n hd1 π ha h0 h3 (m + 1) (by omega)
    refine Submodule.finiteDimensional_of_le (S₂ := fixed (jac (stdBlocks (fun _ : Fin n => 1) hd1) π)
      (PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1)) ?_
    intro w hw u
    have h1 := (Submodule.mem_iInf _).1 hw u
    have h2 : (jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) - 1) w = 0 := h1
    have h3' : jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) w = w := by
      simpa [sub_eq_zero] using h2
    simpa using h3'
  obtain ⟨f, hf0, hf⟩ := GlobalTheory.T.generalized_eigenvector_exists (Levi k (fun _ : Fin n => Fin 1))
    (Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)))
    (jac (stdBlocks (fun _ : Fin n => 1) hd1) π) hcomm
    (fun m => PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1) hanti hpow hsm hfd
    (GlobalTheory.CompanionTheory.PinLift.torusCharHom ξ) v hv0 hv
  obtain ⟨g, w, hg⟩ := GlobalTheory.T.jacquet_cuspidal_support_of_functional n π ξ hξ hd f hf0 hf
  obtain ⟨G, x, hx⟩ := GlobalTheory.CompanionTheory.FrobInv.exists_map_prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd π hs g ⟨w, hg⟩
  refine ⟨G, ?_⟩
  have hso : IsSimpleOrder (Subrepresentation π) := hirr
  have hk : ∀ y, y ∈ G.ker.toSubmodule ↔ G y = 0 := fun y => Iff.rfl
  rcases eq_bot_or_eq_top G.ker with h0' | h0'
  · refine (injective_iff_map_eq_zero G.toLinearMap).2 fun y hy => ?_
    have hy' : y ∈ G.ker.toSubmodule := (hk y).2 hy
    rw [h0'] at hy'
    exact (Submodule.mem_bot ℂ).1 hy'
  · refine absurd ((hk x).1 ?_) hx
    rw [h0']
    trivial

end GlobalTheory.CompanionTheory.GlFrob
