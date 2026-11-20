import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormVEqAbsNorm

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.ChiMuArtin

/- English proof (translation)
Introduce `hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i j hj hae w hw B σ hB hσ`. Take `⟨Bf, hBf⟩` from `hae`. Take `⟨art, ha⟩` from `hArt D.host.E X.nd.Om`. Set `C' : GlobalTheory.Mem.Chr.HFrame D.host (eExp D)` to `⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩`. Take `⟨n0, h0⟩` from `GlobalTheory.GalChar.exists_isAlgPos_mu0 C' hE j`.

Take `⟨m, hm0, hm⟩` from `tp.xi_fin (X.nd.mu i)`. Establish `hxa : IsAlgPos (tp.xi (X.nd.mu i)) 0` using `isAlgPos_zero_of_orderDvd hm0 hm`. Take `⟨n, hn⟩` from `GlobalTheory.GalChar.block_alg C' ⟨_, GlobalTheory.GalChar.isAlgPos_mul h0 hxa⟩`. Establish `hn' : IsAlgPos (GlobalTheory.GalChar.block (tp.tup (X.nd.mu i) j) cf.eta D.R.r) n` using `hn`. Use `set ι := qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i)) with hι`.

Take `⟨r, hr, hLr⟩` from `ha.exists_isLAdicOf ι hn'`. Establish `hO` using `X.nd.O_adic i`. Establish `hκ` using `Sp.iq_alg i`. Establish `hρ : Continuous (GlobalTheory.GalChar.inQ (Sp.iq i) (X.nd.chi i 1))` using `GlobalTheory.GalChar.continuous_units _ ((GlobalTheory.GalChar.isEmbedding_toQ hO hκ).continuous.comp (X.nd.chi_cont i 1))`. Establish `hlne : X.nd.l i ≠ 0` using `(Fact.out : (X.nd.l i).Prime).ne_zero`.

Establish `hub : ∀ v, (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt v → (GlobalTheory.GalChar.block (tp.tup (X.nd.mu i) j) cf.eta D.R.r).UnrAt v`. Introduce `v hv x hx`. Rewrite using `[GlobalTheory.GalChar.block_loc (cf.isEta.unr v) hx]`. Establish `h1` using `hv x hx`. Establish `h2` using `cf.isEta.unr v x hx`.

Rewrite `h1` using `[HChar.loc_mul, HChar.loc_inv, h2, inv_one, mul_one]`. Conclude with `h1`. Establish `hval : ∀ v, ((X.nd.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal → (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt v → ∀ (A' : ValuationSubring X.nd.Om) (τ : G D.host.E X.nd.Om), IsPlaceOver A' v → IsFrob (F` using `D.host.E) A' (normV v) τ → ι ((r τ : (Qbar (X.nd.l i))ˣ) : Qbar (X.nd.l i)) = (((tp.tup (X.nd.mu i) j * cf.eta⁻¹).val v)⁻¹ : ℂˣ).1 * ((normV v : ℕ) : ℂ) ^ (((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) : ℝ) : ℂ) := by`. Introduce `v hl hu A' τ hA' hτ`. Rewrite using `[hLr.frob_unr ha (Or.inl hl) (hub v hu) hA' hτ, map_inv₀, ι.apply_symm_apply, GlobalTheory.GalChar.block_val, mul_inv, ← Complex.cpow_neg, ← Units.val_inv_eq_inv_val, GlobalTheory.ChiLocGal.normV_eq_absNorm]`.

Use `congr 2`. Unfold `Ranks.nV`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hev : ∀ᶠ P in Filter.cofinite, P ∉ Bf` using `Filter.eventually_cofinite.2 (by simpa using Bf.finite_toSet)`.

Establish `heq : GlobalTheory.GalChar.inQ (Sp.iq i) (X.nd.chi i 1) = r`. Use `GlobalTheory.GalChar.eq_of_frob ha hρ hr ?_` and prove the remaining obligations. Use `filter_upwards [hev, GlobalTheory.GalChar.away_ae (E := D.host.E) (X.nd.l i) hlne] with v hv hl A' hA' σ' hσ'`. Use `GlobalTheory.ChiLocGal.frob_any (X.nd.plOm.2 v) hA' (fun τ hτ => ?_) hσ'` and prove the remaining obligations. Take `⟨hu, hv2⟩` from `hBf v hv`.

Apply `Units.ext` to reduce the goal to its premises. Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[hval v hl hu _ τ (X.nd.plOm.2 v) hτ, ← hv2 τ hτ]`. Both sides reduce to the same expression. Establish `hwl : ((X.nd.l i : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal` using `hw.2.1`.

Establish `hwu : (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt w`. Take `⟨-, hwl', hwS, hwQ⟩` from `hw`. Establish `hS` using `X.nd.S_def i w`. Establish `hnS : ¬ (w ∈ placesOver D.host.E (D.host.g 0) ∨ w ∈ placesOver D.host.E (D.host.g 1) ∨ w ∈ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde))` using `fun h => hwS (hS.2 ⟨h, hwl'⟩)`. Use `push Not at hnS`.

Take `⟨hg0, hg1, hd⟩` from `hnS`. Establish `hmu : (cf.mu0 j).UnrAt w` using `(cf.isMu0 j).unr w (fun k => by fin_cases k`. Conclude with `hg0`. Conclude with `hg1)`. Establish `hxi : tp.xi (X.nd.mu i) = cf.delAt (X.nd.l i) * tp.psi (X.nd.w i)`.

Rewrite using `[X.nd.mu_w i, tp.xi_tw, X.nd.w_l i]`. Establish `hdel : (cf.delAt (X.nd.l i)).UnrAt w`. Unfold `CharFrame.delAt`. Use `split_ifs with h`. Rewrite `hd` using `[if_pos h]`.

Conclude with `cf.isDel'.unr w hd`. Rewrite `hd` using `[if_neg h]`. Conclude with `cf.isDel.unr w hd`. Establish `hmem : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i)` using `(X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩`. Establish `hQ : X.nd.Q i = C.Q (X.nd.w i)` using `(Sp.Q_eq _ _ i hmem).trans (Sp.Qc_eq _ _)`.

Establish `hpsi : (tp.psi (X.nd.w i)).UnrAt w`. Use `tp.psi_is (X.nd.w i) (X.nd.w_tw i)` as an intermediate fact. Rewrite `this` using `[X.nd.w_l i]`. Conclude with `(this.ram w).2 (hQ ▸ hwQ)`. Unfold `TupTied.tup`.

Rewrite using `[hxi]`. Conclude with `(hmu.mul (hdel.mul hpsi)).mul (cf.isEta.unr w).inv`. Rewrite using `[← hval w hwl hwu B σ hB hσ, ← heq]`. Both sides reduce to the same expression.
-/
theorem chiMu_frob_all : ∀ (hArt : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (j : Fin D.R.m), j.1 + 1 = X.nd.j i → (∃ Bf : Finset (HeightOneSpectrum (𝓞 D.host.E)), ∀ P ∉ Bf, (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt P ∧ ∀ σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om, IsFrob (F := D.host.E) (X.nd.plOm.1 P) (normV P) σ → (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i))) = (((tp.tup (X.nd.mu i) j * cf.eta⁻¹).val P)⁻¹ : ℂˣ).1 * ((normV P : ℕ) : ℂ) ^ (((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) : ℝ) : ℂ)) → ∀ w, SplitOut X.nd i w → ∀ (B : ValuationSubring X.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om), IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ → (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i))) = (((tp.tup (X.nd.mu i) j * cf.eta⁻¹).val w)⁻¹ : ℂˣ).1 * ((normV w : ℕ) : ℂ) ^ (((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) : ℝ) : ℂ) := by
  intro hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i j hj hae w hw B σ hB hσ
  obtain ⟨Bf, hBf⟩ := hae
  obtain ⟨art, ha⟩ := hArt D.host.E X.nd.Om
  let C' : GlobalTheory.Mem.Chr.HFrame D.host (eExp D) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  obtain ⟨n0, h0⟩ := GlobalTheory.GalChar.exists_isAlgPos_mu0 C' hE j
  obtain ⟨m, hm0, hm⟩ := tp.xi_fin (X.nd.mu i)
  have hxa : IsAlgPos (tp.xi (X.nd.mu i)) 0 := isAlgPos_zero_of_orderDvd hm0 hm
  obtain ⟨n, hn⟩ := GlobalTheory.GalChar.block_alg C' ⟨_, GlobalTheory.GalChar.isAlgPos_mul h0 hxa⟩
  have hn' : IsAlgPos (GlobalTheory.GalChar.block (tp.tup (X.nd.mu i) j) cf.eta D.R.r) n := hn
  set ι := qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i)) with hι
  obtain ⟨r, hr, hLr⟩ := ha.exists_isLAdicOf ι hn'
  have hO := X.nd.O_adic i
  have hκ := Sp.iq_alg i
  have hρ : Continuous (GlobalTheory.GalChar.inQ (Sp.iq i) (X.nd.chi i 1)) :=
    GlobalTheory.GalChar.continuous_units _ ((GlobalTheory.GalChar.isEmbedding_toQ hO hκ).continuous.comp (X.nd.chi_cont i 1))
  have hlne : X.nd.l i ≠ 0 := (Fact.out : (X.nd.l i).Prime).ne_zero

  have hub : ∀ v, (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt v →
      (GlobalTheory.GalChar.block (tp.tup (X.nd.mu i) j) cf.eta D.R.r).UnrAt v := by
    intro v hv x hx
    rw [GlobalTheory.GalChar.block_loc (cf.isEta.unr v) hx]
    have h1 := hv x hx
    have h2 := cf.isEta.unr v x hx
    rw [HChar.loc_mul, HChar.loc_inv, h2, inv_one, mul_one] at h1
    exact h1

  have hval : ∀ v, ((X.nd.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal → (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt v →
      ∀ (A' : ValuationSubring X.nd.Om) (τ : G D.host.E X.nd.Om), IsPlaceOver A' v → IsFrob (F := D.host.E) A' (normV v) τ →
      ι ((r τ : (Qbar (X.nd.l i))ˣ) : Qbar (X.nd.l i)) =
        (((tp.tup (X.nd.mu i) j * cf.eta⁻¹).val v)⁻¹ : ℂˣ).1 *
          ((normV v : ℕ) : ℂ) ^ (((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) : ℝ) : ℂ) := by
    intro v hl hu A' τ hA' hτ
    rw [hLr.frob_unr ha (Or.inl hl) (hub v hu) hA' hτ, map_inv₀, ι.apply_symm_apply, GlobalTheory.GalChar.block_val,
      mul_inv, ← Complex.cpow_neg, ← Units.val_inv_eq_inv_val, GlobalTheory.ChiLocGal.normV_eq_absNorm]
    congr 2
    unfold Ranks.nV
    push_cast
    ring
  have hev : ∀ᶠ P in Filter.cofinite, P ∉ Bf := Filter.eventually_cofinite.2 (by simpa using Bf.finite_toSet)
  have heq : GlobalTheory.GalChar.inQ (Sp.iq i) (X.nd.chi i 1) = r := by
    refine GlobalTheory.GalChar.eq_of_frob ha hρ hr ?_
    filter_upwards [hev, GlobalTheory.GalChar.away_ae (E := D.host.E) (X.nd.l i) hlne] with v hv hl A' hA' σ' hσ'
    refine GlobalTheory.ChiLocGal.frob_any (X.nd.plOm.2 v) hA' (fun τ hτ => ?_) hσ'
    obtain ⟨hu, hv2⟩ := hBf v hv
    apply Units.ext
    apply ι.injective
    rw [hval v hl hu _ τ (X.nd.plOm.2 v) hτ, ← hv2 τ hτ]
    rfl
  have hwl : ((X.nd.l i : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hw.2.1
  have hwu : (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt w := by
    obtain ⟨-, hwl', hwS, hwQ⟩ := hw
    have hS := X.nd.S_def i w
    have hnS : ¬ (w ∈ placesOver D.host.E (D.host.g 0) ∨ w ∈ placesOver D.host.E (D.host.g 1) ∨
        w ∈ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) :=
      fun h => hwS (hS.2 ⟨h, hwl'⟩)
    push Not at hnS
    obtain ⟨hg0, hg1, hd⟩ := hnS
    have hmu : (cf.mu0 j).UnrAt w := (cf.isMu0 j).unr w (fun k => by
      fin_cases k
      · exact hg0
      · exact hg1)
    have hxi : tp.xi (X.nd.mu i) = cf.delAt (X.nd.l i) * tp.psi (X.nd.w i) := by
      rw [X.nd.mu_w i, tp.xi_tw, X.nd.w_l i]
    have hdel : (cf.delAt (X.nd.l i)).UnrAt w := by
      unfold CharFrame.delAt
      split_ifs with h
      · rw [if_pos h] at hd
        exact cf.isDel'.unr w hd
      · rw [if_neg h] at hd
        exact cf.isDel.unr w hd
    have hmem : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
    have hQ : X.nd.Q i = C.Q (X.nd.w i) := (Sp.Q_eq _ _ i hmem).trans (Sp.Qc_eq _ _)
    have hpsi : (tp.psi (X.nd.w i)).UnrAt w := by
      have := tp.psi_is (X.nd.w i) (X.nd.w_tw i)
      rw [X.nd.w_l i] at this
      exact (this.ram w).2 (hQ ▸ hwQ)
    unfold TupTied.tup
    rw [hxi]
    exact (hmu.mul (hdel.mul hpsi)).mul (cf.isEta.unr w).inv
  rw [← hval w hwl hwu B σ hB hσ, ← heq]
  rfl

end GlobalTheory.ChiMuArtin
