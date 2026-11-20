import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLinearApproxTower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExistStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelAction

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, Units.val_mul, ← Matrix.mulVec_mulVec]`. Generalize the expression as in `(β⁻¹).1 *ᵥ z = w at hz`. Conclude with `Subring.sum_mem S (t := Finset.univ) (f := fun j => (y.1 i j : R) * w j) fun j _ => mul_mem (y.1 i j).2 (hz j)`.
-/
theorem conj_mulVec_mem {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) (y : GL (Fin n) S)
    (z : Fin n → R) (hz : ∀ j, ((β⁻¹).1 *ᵥ z) j ∈ S) (i : Fin n) :
    ((β⁻¹).1 *ᵥ ((β * Formalism.UG.bc S.subtype y * β⁻¹).1 *ᵥ z)) i ∈ S := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec]
  generalize (β⁻¹).1 *ᵥ z = w at hz
  exact Subring.sum_mem S (t := Finset.univ) (f := fun j => (y.1 i j : R) * w j) fun j _ => mul_mem (y.1 i j).2 (hz j)

variable {D : D7}

/- English proof (translation)
Establish `hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E))`. Rewrite using `[GlobalTheory.PrincInLevel.eq_latC hβ]`. Conclude with `(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1`. Take `⟨c, hfr, -⟩` from `hβ`. Take `⟨y, hy⟩` from `hk`.

Establish `hy' : β * intGL D.host.F D.host.E V.rank y * β⁻¹ = Formalism.UG.bc (Lev.swapAE D) (finHom V k)` using `hy`. Introduce `z hz`. Use `⟨(finHom V k).1 *ᵥ z - z, sub_mem ?_ hz, (one_nsmul _).symm⟩` and prove the remaining obligations. Rewrite `hz`, the goal using `[hl]`. Establish `h2` using `(hfr _).1 (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz)`.

Establish `h3 : (Formalism.UG.bc (Lev.swapAE D) (finHom V k)).1 *ᵥ (fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E (z i)) ∈ Formalism.L2.Herm.hatL (F` using `D.host.F) Λ := by`. Rewrite using `[← hy']`. Conclude with `(hfr _).2 (conj_mulVec_mem _ β y _ h2)`. Establish `h4` using `GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h3`. Use `h4 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Rewrite using `[AlgEquiv.eq_symm_apply]`. Conclude with `RingHom.map_mulVec (Lev.swapAE D) (finHom V k).1 z i`.
-/
theorem finCong_of_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1) {k : GA D V}
    (hk : Lev.finE V k ∈ St β) : GlobalTheory.Member.FinCong V 1 k := by
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨y, hy⟩ := hk
  have hy' : β * intGL D.host.F D.host.E V.rank y * β⁻¹ = Formalism.UG.bc (Lev.swapAE D) (finHom V k) := hy
  intro z hz
  refine ⟨(finHom V k).1 *ᵥ z - z, sub_mem ?_ hz, (one_nsmul _).symm⟩
  rw [hl] at hz ⊢
  have h2 := (hfr _).1 (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz)
  have h3 : (Formalism.UG.bc (Lev.swapAE D) (finHom V k)).1 *ᵥ
      (fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [← hy']
    exact (hfr _).2 (conj_mulVec_mem _ β y _ h2)
  have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h3
  convert h4 using 1
  funext i
  rw [AlgEquiv.eq_symm_apply]
  exact RingHom.map_mulVec (Lev.swapAE D) (finHom V k).1 z i

/- English proof (translation)
Establish `hh` using `GlobalTheory.Member.LatMove.hat_eq_of_finCong V hk`. Establish `hL` using `GlobalTheory.Member.LatMove.lat_eq_of_hat_eq V hh`. Take `⟨h1, h2, -, -, h5, -⟩` from `GlobalTheory.Member.latG_lattice_and_completion D V 1`. Take `⟨-, -, h3, -⟩` from `GlobalTheory.Member.latG_lattice_and_completion D V k`. Rewrite `h3` using `[hL]`.

Take `⟨f, hf, -⟩` from `GlobalTheory.AdLat.exists_linear_approx_tower D.host.F D.host.E V.rank (latG V 1) (finHom V k) (latG V 1) h1 h2 h3`. Set `e : La ≃ₗ[𝓞 D.host.E] latG V 1` to `(LinearEquiv.ofInjective ι hι.1).trans (LinearEquiv.ofEq _ _ hι.2)`. Establish `he : ∀ a, (e a : Fin V.rank → D.host.E) = ι a` using `fun a => rfl`. Use `⟨e.symm.toLinearMap ∘ₗ f M ∘ₗ e.toLinearMap, fun a => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, ew⟩` from `hf M hM (e a)`.

Use `⟨(finHom V k).1 *ᵥ w, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hh]`. Conclude with `(GlobalTheory.Member.LatMove.mem_hat_iff V k _).2 ⟨w, h5 ▸ hw, rfl⟩`. Establish `e1 : ι ((e.symm.toLinearMap ∘ₗ f M ∘ₗ e.toLinearMap) a) = (f M (e a) : Fin V.rank → D.host.E)`. Rewrite using `[← he]`.

Conclude with `congrArg Subtype.val (e.apply_symm_apply _)`. Rewrite using `[e1]`. Establish `e2 : finVec V (f M (e a) : Fin V.rank → D.host.E) = (finHom V k).1 *ᵥ (finVec V (ι a) + M • w)` using `ew`. Rewrite using `[e2, Matrix.mulVec_add, add_sub_cancel_left]`. Conclude with `map_nsmul (finHom V k).1.mulVecLin M w`.
-/
theorem exists_endo {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) {M : ℕ} (hM : 0 < M) {k : GA D V}
    (hk : GlobalTheory.Member.FinCong V 1 k) : ∃ f : La →ₗ[𝓞 D.host.E] La, ∀ a, ∃ w ∈ latGHat V 1,
      finVec V (ι (f a)) - (finHom V k).1.mulVec (finVec V (ι a)) = M • w := by
  have hh := GlobalTheory.Member.LatMove.hat_eq_of_finCong V hk
  have hL := GlobalTheory.Member.LatMove.lat_eq_of_hat_eq V hh
  obtain ⟨h1, h2, -, -, h5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V k
  rw [hL] at h3
  obtain ⟨f, hf, -⟩ := GlobalTheory.AdLat.exists_linear_approx_tower D.host.F D.host.E V.rank (latG V 1) (finHom V k)
    (latG V 1) h1 h2 h3
  let e : La ≃ₗ[𝓞 D.host.E] latG V 1 := (LinearEquiv.ofInjective ι hι.1).trans (LinearEquiv.ofEq _ _ hι.2)
  have he : ∀ a, (e a : Fin V.rank → D.host.E) = ι a := fun a => rfl
  refine ⟨e.symm.toLinearMap ∘ₗ f M ∘ₗ e.toLinearMap, fun a => ?_⟩
  obtain ⟨w, hw, ew⟩ := hf M hM (e a)
  refine ⟨(finHom V k).1 *ᵥ w, ?_, ?_⟩
  · rw [← hh]
    exact (GlobalTheory.Member.LatMove.mem_hat_iff V k _).2 ⟨w, h5 ▸ hw, rfl⟩
  · have e1 : ι ((e.symm.toLinearMap ∘ₗ f M ∘ₗ e.toLinearMap) a) = (f M (e a) : Fin V.rank → D.host.E) := by
      rw [← he]
      exact congrArg Subtype.val (e.apply_symm_apply _)
    rw [e1]
    have e2 : finVec V (f M (e a) : Fin V.rank → D.host.E) = (finHom V k).1 *ᵥ (finVec V (ι a) + M • w) := ew
    rw [e2, Matrix.mulVec_add, add_sub_cancel_left]
    exact map_nsmul (finHom V k).1.mulVecLin M w

/- English proof (translation)
Introduce `hc`. Apply `PP'.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[eq_top_iff, ← l.coprime]`. Use `sup_le h' (Ideal.map_le_iff_le_comap.2 fun c hc' => ?_)` and prove the remaining obligations. Take `⟨c', h1, h2⟩` from `hc c (h hc')`.

Establish `e : H.bar c = c'` using `RingOfIntegers.ext ((H.bar_eq c).trans h2.symm)`. Express the relevant statement in the definitionally equal form `H.bar c ∈ PP'.asIdeal`. Rewrite using `[e]` and apply the resulting hypothesis.
-/
theorem not_isConjPl {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H)
    {PP PP' : Pl D.host.E} (h : l.Mb ≤ PP.asIdeal) (h' : l.Mb ≤ PP'.asIdeal) : ¬ Lev.IsConjPl PP PP' := by
  intro hc
  apply PP'.isPrime.ne_top
  rw [eq_top_iff, ← l.coprime]
  refine sup_le h' (Ideal.map_le_iff_le_comap.2 fun c hc' => ?_)
  obtain ⟨c', h1, h2⟩ := hc c (h hc')
  have e : H.bar c = c' := RingOfIntegers.ext ((H.bar_eq c).trans h2.symm)
  change H.bar c ∈ PP'.asIdeal
  rwa [e]

/- English proof (translation)
Establish `hj : InR D ((i : ℕ) + 1)` using `⟨Nat.le_add_left _ _, i.2⟩`. Take `⟨hr, g, e, F, ik, φ, th, h, -⟩` from `hT.adPin _ hj _ T.toCore.good_σ₀`. Establish `hV` using `hT.spaceW _ hj _ T.toCore.good_σ₀`. Establish `key : ∀ (V : HSp D) (hr : V.rank = D.R.r), V = Wc D i → LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) → LatEmb (Wc D i) (iotaW T i)`. Introduce and unpack `V hr rfl h`.

Conclude with `h`. Conclude with `key _ hr hV h`.
-/
theorem latEmb_iotaW (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) : LatEmb (Wc D i) (iotaW T i) := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨hr, g, e, F, ik, φ, th, h, -⟩ := hT.adPin _ hj _ T.toCore.good_σ₀
  have hV := hT.spaceW _ hj _ T.toCore.good_σ₀
  have key : ∀ (V : HSp D) (hr : V.rank = D.R.r), V = Wc D i →
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatEmb (Wc D i) (iotaW T i) := by
    rintro V hr rfl h
    exact h
  exact key _ hr hV h

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hR ⟨tie⟩ hpb i`. Establish `hT` using `tie.laws`. Establish `hβ` using `hR.lev.βW i`. Establish `hle : ∀ PP ∈ R.Pg, T.Q.l.Mb ≤ PP.asIdeal`. Introduce `PP hP`.

Take `⟨k, hk⟩` from `(hR.lev.Pg PP).1 hP`. Rewrite using `[hT.half.2]`. Use `(Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ k))).trans ?_` and prove the remaining obligations. Rewrite using `[hpb, ← show PP.under (𝓞 D.host.K) = R.C.P.pb k from hk]`. Conclude with `Ideal.map_comap_le`.

Establish `hlift : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv)`. Take `⟨c, hc⟩` from `hβ`. Use `GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP h PP' h' => ?_) (Finset.disjoint_empty_right _)` and prove the remaining obligations. Break down `h' with h' | h'` into its components or cases. Conclude with `not_isConjPl T.Q.l (hle PP h) (hle PP' h')`.

Conclude with `absurd h' (Finset.notMem_empty _)`. Establish `hM : 0 < T.Q.l.M` using `lt_of_lt_of_le (by norm_num) T.Q.l.three_le`. Use `choose k hk using fun g => hlift (R.eG g)`. Use `choose f hf using fun g => exists_endo (iotaW T i) (latEmb_iotaW T hT i) hM (finCong_of_mem_St hβ (parLev_St (hk g).2.1))`. Conclude with `⟨f, fun g => ⟨k g, hk g, fun a _ => hf g a⟩⟩`.
-/
theorem exists_levIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ i : Fin D.R.m, ∃ lev, LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR ⟨tie⟩ hpb i
  have hT := tie.laws
  have hβ := hR.lev.βW i
  have hle : ∀ PP ∈ R.Pg, T.Q.l.Mb ≤ PP.asIdeal := by
    intro PP hP
    obtain ⟨k, hk⟩ := (hR.lev.Pg PP).1 hP
    rw [hT.half.2]
    refine (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ k))).trans ?_
    rw [hpb, ← show PP.under (𝓞 D.host.K) = R.C.P.pb k from hk]
    exact Ideal.map_comap_le
  have hlift : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
    obtain ⟨c, hc⟩ := hβ
    refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP h PP' h' => ?_) (Finset.disjoint_empty_right _)
    rcases h' with h' | h'
    · exact not_isConjPl T.Q.l (hle PP h) (hle PP' h')
    · exact absurd h' (Finset.notMem_empty _)
  have hM : 0 < T.Q.l.M := lt_of_lt_of_le (by norm_num) T.Q.l.three_le
  choose k hk using fun g => hlift (R.eG g)
  choose f hf using fun g => exists_endo (iotaW T i) (latEmb_iotaW T hT i) hM
    (finCong_of_mem_St hβ (parLev_St (hk g).2.1))
  exact ⟨f, fun g => ⟨k g, hk g, fun a _ => hf g a⟩⟩

end GlobalTheory.LevelAction
