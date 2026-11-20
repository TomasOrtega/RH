import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HermitianLatticeSelfDual

open GlobalTheory.TripleDarboux
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars)

/- English proof (translation)
Use `⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ?_)⟩` and prove the remaining obligations. Establish `e : ∑ i, ∑ j, star (x i) * (sgn true V).gram i j * y j = -∑ i, ∑ j, star (x i) * V.gram i j * y j`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `show star (x i) * (-V.gram i j) * y j = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `⟨fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩, fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩⟩`.
-/
private theorem selfDual_neg {D : D7} {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : IsSelfDualC V Λ) : IsSelfDualC (sgn true V) Λ := by
  refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ?_)⟩
  have e : ∑ i, ∑ j, star (x i) * (sgn true V).gram i j * y j = -∑ i, ∑ j, star (x i) * V.gram i j * y j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show star (x i) * (-V.gram i j) * y j = _
    ring
  rw [e]
  exact ⟨fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩, fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩⟩

/- English proof (translation)
Establish `hlat` using `Formalism.L2.Col.brp_starLat_lattice _ _ hsd.1`. Take `⟨bas, hbas⟩` from `exists_bas B _ hlat`. Establish `eJ : ∀ w, ((-1 : D.host.E) • S.gram).map (B.emb w).1 = -((gramAt D S (τf w)).map star)` using `fun w => by`. Use extensionality with `a b`. Simplify using `[gramAt, hB]`.

Use `⟨_, bas, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => GlobalTheory.TripleSpace.mem_starLat_iff_form S hsd y, fun w => ?_, hbas⟩, fun y => Iff.rfl⟩` and prove the remaining obligations. Use `show star (((-1 : D.host.E) • S.gram) b a) = ((-1 : D.host.E) • S.gram) a b`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, star_one, GlobalTheory.TripleSpace.star_gram]`. Use `show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((-1 : D.host.E) • S.gram).map (B.emb w).1) _ _`. Rewrite using `[eJ]`.

Conclude with `GlobalTheory.TripleSpace.hasSig_neg_of_hasSignature (hasSignature_map_conj (hsig _))`. Use `show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((-1 : D.host.E) • S.gram).map (B.emb w).1) _`. Rewrite using `[eJ]`. Conclude with `GlobalTheory.TripleSpace.isCartan_neg_conj (hs _)`.
-/
private theorem herm_of_lat {D : D7} (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hB : ∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) (S : HSp D)
    (Λ₀ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (hsd : IsSelfDualC S Λ₀)
    (s : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (hs : ∀ τ, IsCartanInv (gramAt D S τ) (s τ)) {p q : ℕ} (hsig : ∀ τ, Formalism.UG.HasSignature (gramAt D S τ) p q) :
    ∃ Λ bas, Spc.IsHerm D.sp.cm.sig B (Spc.mk ((-1 : D.host.E) • S.gram) Λ (fun w => -s (τf w)) bas) q p ∧
      ∀ y, y ∈ Λ ↔ star y ∈ Λ₀ := by
  have hlat := Formalism.L2.Col.brp_starLat_lattice _ _ hsd.1
  obtain ⟨bas, hbas⟩ := exists_bas B _ hlat
  have eJ : ∀ w, ((-1 : D.host.E) • S.gram).map (B.emb w).1 = -((gramAt D S (τf w)).map star) := fun w => by
    ext a b; simp [gramAt, hB]
  refine ⟨_, bas, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => GlobalTheory.TripleSpace.mem_starLat_iff_form S hsd y, fun w => ?_, hbas⟩,
    fun y => Iff.rfl⟩
  · show star (((-1 : D.host.E) • S.gram) b a) = ((-1 : D.host.E) • S.gram) a b
    simp only [Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, star_one, GlobalTheory.TripleSpace.star_gram]
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((-1 : D.host.E) • S.gram).map (B.emb w).1) _ _
    rw [eJ]
    exact GlobalTheory.TripleSpace.hasSig_neg_of_hasSignature (hasSignature_map_conj (hsig _))
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((-1 : D.host.E) • S.gram).map (B.emb w).1) _
    rw [eJ]
    exact GlobalTheory.TripleSpace.isCartan_neg_conj (hs _)

open scoped ComplexOrder in

/- English proof (translation)
Set `e' : Fin X.rank ⊕ Fin (zeroSp D).rank ≃ Fin k` to `(Equiv.sumEmpty (Fin X.rank) (Fin 0)).trans e.symm`. Establish `hJ : D.host.xi0 • (X.gramᵀ).submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram X (zeroSp D) e'` using `congrArg (D.host.xi0 • ·) (blk_empty e _ _).symm`. Establish `hZ` using `GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D (zeroSp D)`. Establish `hlat` using `GlobalTheory.SkewLat.isLattice_pairLat GlobalTheory.SkewLat.DualPair.AA_ne hA.1 hZ.1 e'`. Take `⟨bas, hbas⟩` from `exists_bas B _ hlat`.

Establish `hsub : Subsingleton (Matrix (Fin (zeroSp D).rank) (Fin (zeroSp D).rank) ℂ)` using `inferInstanceAs (Subsingleton (Matrix (Fin 0) (Fin 0) ℂ))`. Establish `hsub' : Subsingleton (Fin (zeroSp D).rank → D.host.E)` using `inferInstanceAs (Subsingleton (Fin 0 → D.host.E))`. Use `⟨_, bas, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => ?_, fun w => ?_, hbas⟩, fun y => ?_⟩` and prove the remaining obligations. Use `show star (D.host.xi0 * X.gram (e a) (e b)) = -(D.host.xi0 * X.gram (e b) (e a))`. Rewrite using `[star_mul', GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D, GlobalTheory.TripleSpace.star_gram, neg_mul]`.

Use `show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (Complex.I • (D.host.xi0 • (X.gramᵀ).submatrix e e).map (B.emb w).1) _ _`. Rewrite using `[hJ, GlobalTheory.SkewLat.I_smul_skewGram_map _ _ e' (τf w) (B.emb w).1 (hB w)]`. Apply the tactic sequence `have h0 : Formalism.UG.HasSignature (gramAt D (zeroSp D) (τf w)) 0 0 := ⟨(Equiv.sumEmpty (Fin 0) (Fin 0)).symm, 1, by ext (a | a) <;> exact a.elim0⟩`. Conclude with `GlobalTheory.SkewLat.hasSig_blk e' _ _ (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (hsig _) h0`. Use `show y ∈ _ ↔ ∀ x ∈ _, ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (D.host.xi0 • (X.gramᵀ).submatrix e e) y x))`.

Rewrite using `[hJ]`. Conclude with `GlobalTheory.SkewLat.dual_pairLat (fun c hc => GlobalTheory.SkewLat.star_mem_AA hc) _ _ hA hZ e' y`. Use `show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • (D.host.xi0 • (X.gramᵀ).submatrix e e).map (B.emb w).1) (((s (τf w)).submatrix e e).map conj)`. Rewrite using `[hJ, GlobalTheory.SkewLat.I_smul_skewGram_map _ _ e' (τf w) (B.emb w).1 (hB w), ← blk_empty e (s (τf w)) 1]`. Establish `h0 : IsCartanInv (gramAt D (zeroSp D) (τf w)) 1` using `⟨Subsingleton.elim _ _, Subsingleton.elim _ _, by`.

Rewrite using `[Subsingleton.elim (gramAt D (zeroSp D) (τf w) * 1) 1]`. Conclude with `Matrix.PosDef.one⟩`. Conclude with `GlobalTheory.SkewLat.isCartan_blk e' _ _ _ _ (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (hs _) h0`. Use `GlobalTheory.SkewLat.mem_pairLat.trans ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim (fun k => y (e' (.inr k))) 0]`.

Conclude with `zero_mem _`.
-/
private theorem skew_of_lat {D : D7} (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hB : ∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank)
    (Λ₀ : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)) (hA : IsSelfDualC X Λ₀)
    (s : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ)
    (hs : ∀ τ, IsCartanInv (gramAt D X τ) (s τ)) {p q : ℕ} (hsig : ∀ τ, Formalism.UG.HasSignature (gramAt D X τ) p q) :
    ∃ Λ bas, Spc.IsSkew D.sp.cm.sig B (Spc.mk (D.host.xi0 • (X.gramᵀ).submatrix e e) Λ
      (fun w => ((s (τf w)).submatrix e e).map conj) bas) p q ∧
      ∀ y, y ∈ Λ ↔ (fun k => y (e.symm k)) ∈ GlobalTheory.SkewLat.scLat D.host.AA Λ₀ := by
  let e' : Fin X.rank ⊕ Fin (zeroSp D).rank ≃ Fin k := (Equiv.sumEmpty (Fin X.rank) (Fin 0)).trans e.symm
  have hJ : D.host.xi0 • (X.gramᵀ).submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram X (zeroSp D) e' :=
    congrArg (D.host.xi0 • ·) (blk_empty e _ _).symm
  have hZ := GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D (zeroSp D)
  have hlat := GlobalTheory.SkewLat.isLattice_pairLat GlobalTheory.SkewLat.DualPair.AA_ne hA.1 hZ.1 e'
  obtain ⟨bas, hbas⟩ := exists_bas B _ hlat
  have hsub : Subsingleton (Matrix (Fin (zeroSp D).rank) (Fin (zeroSp D).rank) ℂ) :=
    inferInstanceAs (Subsingleton (Matrix (Fin 0) (Fin 0) ℂ))
  have hsub' : Subsingleton (Fin (zeroSp D).rank → D.host.E) :=
    inferInstanceAs (Subsingleton (Fin 0 → D.host.E))
  refine ⟨_, bas, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => ?_, fun w => ?_, hbas⟩, fun y => ?_⟩
  · show star (D.host.xi0 * X.gram (e a) (e b)) = -(D.host.xi0 * X.gram (e b) (e a))
    rw [star_mul', GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D, GlobalTheory.TripleSpace.star_gram, neg_mul]
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (Complex.I • (D.host.xi0 • (X.gramᵀ).submatrix e e).map (B.emb w).1) _ _
    rw [hJ, GlobalTheory.SkewLat.I_smul_skewGram_map _ _ e' (τf w) (B.emb w).1 (hB w)]
    have h0 : Formalism.UG.HasSignature (gramAt D (zeroSp D) (τf w)) 0 0 :=
      ⟨(Equiv.sumEmpty (Fin 0) (Fin 0)).symm, 1, by ext (a | a) <;> exact a.elim0⟩
    exact GlobalTheory.SkewLat.hasSig_blk e' _ _ (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (hsig _) h0
  · show y ∈ _ ↔ ∀ x ∈ _, ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E
      (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (D.host.xi0 • (X.gramᵀ).submatrix e e) y x))
    rw [hJ]
    exact GlobalTheory.SkewLat.dual_pairLat (fun c hc => GlobalTheory.SkewLat.star_mem_AA hc) _ _ hA hZ e' y
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • (D.host.xi0 • (X.gramᵀ).submatrix e e).map (B.emb w).1)
      (((s (τf w)).submatrix e e).map conj)
    rw [hJ, GlobalTheory.SkewLat.I_smul_skewGram_map _ _ e' (τf w) (B.emb w).1 (hB w), ← blk_empty e (s (τf w)) 1]
    have h0 : IsCartanInv (gramAt D (zeroSp D) (τf w)) 1 :=
      ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, by
        rw [Subsingleton.elim (gramAt D (zeroSp D) (τf w) * 1) 1]; exact Matrix.PosDef.one⟩
    exact GlobalTheory.SkewLat.isCartan_blk e' _ _ _ _ (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (hs _) h0
  · refine GlobalTheory.SkewLat.mem_pairLat.trans ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rw [Subsingleton.elim (fun k => y (e' (.inr k))) 0]
    exact zero_mem _

/- English proof (translation)
Establish `hν : IsHeckeChar D (α / β)` using `⟨h.hecA.1.div' h.hecB.1, fun x => by rw [MonoidHom.div_apply, h.hecA.2, h.hecB.2, div_one]⟩`. Establish `hr : ResEta D (α / β) 0`. Use `resEta_mul h.resA (resEta_inv h.resB)` as an intermediate fact. Rewrite `this` using `[← div_eq_mul_inv]`. Establish `h1` using `h.rank`.

Take `⟨m, hm⟩` from `h.even`. Conclude with `resEta_parity this (by omega)`. Establish `hT : ∀ v, v ∈ S.image (fun w => w.under (𝓞 D.host.F)) ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v` using `fun v => Finset.mem_image`. Use `⟨S.image (fun w => w.under (𝓞 D.host.F)), hT, fun v hv => ?_, fun w hw hu => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨ε, hε⟩` from `GlobalTheory.StabDense.exists_placeIdem (D := D) v`.

Establish `h3` using `(hS v ε hε).1 ((hT v).1 hv)`. Take `⟨h2, -, h4⟩` from `(h.ram v ε hε).resolve_left fun hu => h3 fun x a b c => by`. Rewrite using `[MonoidHom.div_apply, hu.1 x a b c, hu.2 x a b c, div_one]`. Use `⟨?_, h4⟩` and prove the remaining obligations. Take `⟨t⟩` from `GlobalTheory.T.nonempty_algHom_completion_of_split_place D v ε hε h2`.

Take `⟨w, hw, hwv⟩` from `(hT v).1 hv`. Establish `hmem : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 D.host.E)` using `⟨w.isPrime, ⟨by rw [← hwv]; rfl⟩⟩`. Rewrite `hmem` using `[GlobalTheory.AdelicU.primesOver_eq_split (GlobalTheory.AdelicU.isCMExt_host D) t]`. Break down `hmem with h5 | h5` into its components or cases. Conclude with `⟨t, (HeightOneSpectrum.ext h5 : w = _) ▸ hw⟩`.

Conclude with `⟨_, (HeightOneSpectrum.ext h5 : w = _) ▸ hw⟩`. Take `⟨ε, hε⟩` from `GlobalTheory.StabDense.exists_placeIdem (D := D) (w.under (𝓞 D.host.F))`. Conclude with `(hS _ ε hε).1 ((hT _).1 hw) (GlobalTheory.T.heckeChar_unramified_place_of_unramified_one_prime D _ hν hr _ ε hε w rfl hu)`. Take `⟨ε, hε⟩` from `GlobalTheory.StabDense.exists_placeIdem (D := D) (w.under (𝓞 D.host.F))`. Establish `hu` using `(hS _ ε hε).2 fun u hu e => hw ((hT _).2 ⟨u, hu, e⟩)`.

Conclude with `⟨GlobalTheory.BasePairChar.unrAt_of_unramAt hε hu.1 rfl, GlobalTheory.BasePairChar.unrAt_of_unramAt hε hu.2 rfl⟩`.
-/
private theorem ram_set {D : D7} {W W₁ X : HSp D} {α β : (AE D)ˣ →* Circle} (h : IsTriple W W₁ X α β)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hS : ∀ v ε, IsPlaceIdem D v ε → ((∃ w ∈ S, w.under (𝓞 D.host.F) = v) → ¬ GlobalTheory.WeilParts.UnramAt ε (α / β)) ∧
      ((∀ w ∈ S, w.under (𝓞 D.host.F) ≠ v) → GlobalTheory.WeilParts.UnramAt ε α ∧ GlobalTheory.WeilParts.UnramAt ε β)) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 D.host.F)), (∀ v, v ∈ T ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) ∧
      (∀ v ∈ T, (∃ t : D.host.E →ₐ[D.host.F] Fv D.host.F v, splitPrime t ∈ S) ∧
        ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) ∧
      (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∈ T → ¬ GlobalTheory.LFun.UnrAt (α / β) w) ∧
      ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ T → GlobalTheory.LFun.UnrAt α w ∧ GlobalTheory.LFun.UnrAt β w := by
  have hν : IsHeckeChar D (α / β) :=
    ⟨h.hecA.1.div' h.hecB.1, fun x => by rw [MonoidHom.div_apply, h.hecA.2, h.hecB.2, div_one]⟩
  have hr : ResEta D (α / β) 0 := by
    have := resEta_mul h.resA (resEta_inv h.resB)
    rw [← div_eq_mul_inv] at this
    have h1 := h.rank
    obtain ⟨m, hm⟩ := h.even
    exact resEta_parity this (by omega)
  have hT : ∀ v, v ∈ S.image (fun w => w.under (𝓞 D.host.F)) ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v :=
    fun v => Finset.mem_image
  refine ⟨S.image (fun w => w.under (𝓞 D.host.F)), hT, fun v hv => ?_, fun w hw hu => ?_, fun w hw => ?_⟩
  · obtain ⟨ε, hε⟩ := GlobalTheory.StabDense.exists_placeIdem (D := D) v
    have h3 := (hS v ε hε).1 ((hT v).1 hv)
    obtain ⟨h2, -, h4⟩ := (h.ram v ε hε).resolve_left fun hu => h3 fun x a b c => by
      rw [MonoidHom.div_apply, hu.1 x a b c, hu.2 x a b c, div_one]
    refine ⟨?_, h4⟩
    obtain ⟨t⟩ := GlobalTheory.T.nonempty_algHom_completion_of_split_place D v ε hε h2
    obtain ⟨w, hw, hwv⟩ := (hT v).1 hv
    have hmem : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 D.host.E) :=
      ⟨w.isPrime, ⟨by rw [← hwv]; rfl⟩⟩
    rw [GlobalTheory.AdelicU.primesOver_eq_split (GlobalTheory.AdelicU.isCMExt_host D) t] at hmem
    rcases hmem with h5 | h5
    · exact ⟨t, (HeightOneSpectrum.ext h5 : w = _) ▸ hw⟩
    · exact ⟨_, (HeightOneSpectrum.ext h5 : w = _) ▸ hw⟩
  · obtain ⟨ε, hε⟩ := GlobalTheory.StabDense.exists_placeIdem (D := D) (w.under (𝓞 D.host.F))
    exact (hS _ ε hε).1 ((hT _).1 hw) (GlobalTheory.T.heckeChar_unramified_place_of_unramified_one_prime D _ hν hr _ ε hε w rfl hu)
  · obtain ⟨ε, hε⟩ := GlobalTheory.StabDense.exists_placeIdem (D := D) (w.under (𝓞 D.host.F))
    have hu := (hS _ ε hε).2 fun u hu e => hw ((hT _).2 ⟨u, hu, e⟩)
    exact ⟨GlobalTheory.BasePairChar.unrAt_of_unramAt hε hu.1 rfl, GlobalTheory.BasePairChar.unrAt_of_unramAt hε hu.2 rfl⟩

end UpperTheory.HermitianLatticeSelfDual

attribute [-instance] Formalism.IndefR.Fin.intEF in
/- English proof (translation)
Use `open GlobalTheory.TripleDarboux UpperTheory.HermitianLatticeSelfDual in`. Introduce `D ψ hψ W W₁ X A A₁ B α β h ωA ωB hA hB ΛW ΛW₁ ΛX₀ sW sW₁ sX S hS e`. Use `choose τf hτf using (GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace (D := D))`. Use `choose a b ha hb hab using h.gap`. Take `⟨mα, hα, eα⟩` from `GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp α a ha τf hτf`.

Take `⟨mβ, hβ, eβ⟩` from `GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp β b hb τf hτf`. Take `⟨T, hT0, hT1, hT2, hT3⟩` from `ram_set h S hS`. Take `⟨v₁, hv₁, hv₁s, ⟨τ₁⟩⟩` from `exists_good_place D T`. Set `Bs : Base D.host.F D.host.E` to `⟨ψ, fun w => ⟨_, hτf w⟩, mα, mβ, T, fun v => (hT1 v v.2).1.choose, v₁, τ₁⟩`. Establish `hBs : Bs.IsGood D.sp.cm.sig` using `base_isGood Bs hψ fun v hv => (hT1 v hv).2`.

Establish `hemb : ∀ w x, (Bs.emb w).1 x = conj (tauE D (τf w) x)` using `fun _ _ => rfl`. Take `⟨p, q, hsig, hn1, hn2⟩` from `h.sig`. Establish `hneg : ∀ τ, gramAt D (sgn true W) τ = -gramAt D W τ` using `fun τ => by ext i j; simp [gramAt, neg_gram]`. Take `⟨ΛV, basV, hV, lV⟩` from `herm_of_lat Bs τf hemb (sgn true W) ΛW (selfDual_neg sW) (fun τ => sgnM true (A.cart τ)) (fun τ => isCartanInv_sgn true W τ (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ)) (fun τ => by rw [hneg]; exact hasSignature_neg (hsig τ).1)`. Establish `eJ : (-1 : D.host.E) • (sgn true W).gram = (1 : D.host.E) • W.gram`.

Rewrite using `[neg_gram, neg_smul, one_smul, one_smul, neg_neg]`. Establish `eθ : (fun w => -sgnM true (A.cart (τf w))) = fun w => A.cart (τf w)` using `funext fun w => neg_neg _`. Rewrite `hV` using `[eJ, eθ]`. Take `⟨ΛV', basV', hV', lV'⟩` from `herm_of_lat Bs τf hemb W₁ ΛW₁ sW₁ A₁.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A₁) fun τ => (hsig τ).2.1`. Take `⟨ΛX, basX, hX, lX⟩` from `skew_of_lat Bs τf hemb X e ΛX₀ sX B.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B) fun τ => (hsig τ).2.2`.

Establish `e3 : X.rank - (p + q) = W.rank + W₁.rank - (p + q)` using `by rw [h.rank]`. Rewrite `hX` using `[e3]`. Take `⟨Mo, hMo⟩` from `exists_model Bs hBs W _ _ hV hX 1 one_ne_zero rfl`. Take `⟨Mo', hMo'⟩` from `exists_model Bs hBs W₁ _ _ hV' hX (-1) (neg_ne_zero.2 one_ne_zero) rfl`. Take `⟨om, hom, htr⟩` from `exists_weil Bs hBs true W X e _ _ hV hX 1 rfl (by rw [neg_gram, one_smul, neg_neg]) rfl Mo hMo hA`.

Take `⟨om', hom', htr'⟩` from `exists_weil Bs hBs false W₁ X e _ _ hV' hX (-1) rfl (neg_one_smul _ _) rfl Mo' hMo' hB`. Establish `hr` using `h.rank`. Establish `hev` using `h.even`. Establish `h2 : Module.finrank D.host.F D.host.E = 2` using `D.sp.cm.deg2`. Establish `hTe : (⟨α, β, T, ∅⟩ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E).T = T` using `by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars.T]`.

Use `⟨Bs, ⟨p, q, _, _, _, Mo, Mo'⟩, ⟨α, β, T, ∅⟩, om, om', ⟨rfl, rfl, rfl, rfl, fun w => ⟨τf w, fun _ => rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, ⟨hBs, ?_, ?_, hom, hom'⟩, htr, htr', ⟨lV, lX⟩, ⟨lV', lX⟩, hTe, hT0, fun v => (hT1 v v.2).1.choose_spec⟩` and prove the remaining obligations. Use `⟨by omega, hr ▸ hev, fun w => ?_, ?_, hn2, hV, hV', hX, hMo, hMo'⟩` and prove the remaining obligations. Establish `h1` using `eα w`. Establish `h3` using `eβ w`. Establish `h4` using `hab (τf w)`.

Rewrite `h4` using `[hr]`. Establish `: (((W.rank + W₁.rank : ℕ) : ℤ) : ℚ) < ((mα w - mβ w : ℤ) : ℚ)`. Move the coercions through the operations in `at h4 ⊢`. Rewrite using `[h1, h3]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `this` after adjusting the coercions. Take `⟨m, hm⟩` from `hev show 2 * (p + q) + 1 < (W.rank - W₁.rank) / 2`. Use linear arithmetic over natural numbers and integers. Use `⟨h.hecA, h.hecB, GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resA), GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resB), hα, hβ, Finset.disjoint_empty_right _, hTe.le, fun w hw => hT2 w (hTe ▸ …` and prove the remaining obligations. Rewrite using `[hTe]`.

Conclude with `h0`. Rewrite using `[hTe]`. Conclude with `h0`.
-/
theorem UpperTheory.exists_lattice_theta_data_of_ramification_places_CMDatum :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
        ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
        ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
        ∀ (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (ΛW₁ : Submodule (𝓞 D.host.E) (Fin W₁.rank → D.host.E))
          (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)), IsSelfDualC W ΛW → IsSelfDualC W₁ ΛW₁ → IsSelfDualC X ΛX →
        ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))),
        (∀ v ε, IsPlaceIdem D v ε → ((∃ w ∈ S, w.under (𝓞 D.host.F) = v) → ¬ GlobalTheory.WeilParts.UnramAt ε (α / β)) ∧
          ((∀ w ∈ S, w.under (𝓞 D.host.F) ≠ v) → GlobalTheory.WeilParts.UnramAt ε α ∧ GlobalTheory.WeilParts.UnramAt ε β)) →
        ∀ e : Fin (W.rank + W₁.rank) ≃ Fin X.rank,
          ∃ (Bs : Base D.host.F D.host.E)
            (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
            (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
            (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' ∧
            GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) ∧
            GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) ∧
            IsLat e Γ.V Γ.W ΛW ΛX ∧ IsLat e Γ.V' Γ.W ΛW₁ ΛX ∧ Xc.T = Bs.P ∧
            (∀ v, v ∈ Bs.P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) ∧ ∀ v : Bs.P, splitPrime (Bs.τ v) ∈ S := by
  open GlobalTheory.TripleDarboux UpperTheory.HermitianLatticeSelfDual in
  intro D ψ hψ W W₁ X A A₁ B α β h ωA ωB hA hB ΛW ΛW₁ ΛX₀ sW sW₁ sX S hS e
  choose τf hτf using (GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace (D := D))
  choose a b ha hb hab using h.gap
  obtain ⟨mα, hα, eα⟩ := GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp α a ha τf hτf
  obtain ⟨mβ, hβ, eβ⟩ := GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp β b hb τf hτf
  obtain ⟨T, hT0, hT1, hT2, hT3⟩ := ram_set h S hS
  obtain ⟨v₁, hv₁, hv₁s, ⟨τ₁⟩⟩ := exists_good_place D T
  let Bs : Base D.host.F D.host.E :=
    ⟨ψ, fun w => ⟨_, hτf w⟩, mα, mβ, T, fun v => (hT1 v v.2).1.choose, v₁, τ₁⟩
  have hBs : Bs.IsGood D.sp.cm.sig := base_isGood Bs hψ fun v hv => (hT1 v hv).2
  have hemb : ∀ w x, (Bs.emb w).1 x = conj (tauE D (τf w) x) := fun _ _ => rfl
  obtain ⟨p, q, hsig, hn1, hn2⟩ := h.sig
  have hneg : ∀ τ, gramAt D (sgn true W) τ = -gramAt D W τ := fun τ => by ext i j; simp [gramAt, neg_gram]
  obtain ⟨ΛV, basV, hV, lV⟩ := herm_of_lat Bs τf hemb (sgn true W) ΛW (selfDual_neg sW) (fun τ => sgnM true (A.cart τ))
    (fun τ => isCartanInv_sgn true W τ (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ))
    (fun τ => by rw [hneg]; exact hasSignature_neg (hsig τ).1)
  have eJ : (-1 : D.host.E) • (sgn true W).gram = (1 : D.host.E) • W.gram := by
    rw [neg_gram, neg_smul, one_smul, one_smul, neg_neg]
  have eθ : (fun w => -sgnM true (A.cart (τf w))) = fun w => A.cart (τf w) := funext fun w => neg_neg _
  rw [eJ, eθ] at hV
  obtain ⟨ΛV', basV', hV', lV'⟩ := herm_of_lat Bs τf hemb W₁ ΛW₁ sW₁ A₁.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A₁)
    fun τ => (hsig τ).2.1
  obtain ⟨ΛX, basX, hX, lX⟩ := skew_of_lat Bs τf hemb X e ΛX₀ sX B.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B)
    fun τ => (hsig τ).2.2
  have e3 : X.rank - (p + q) = W.rank + W₁.rank - (p + q) := by rw [h.rank]
  rw [e3] at hX
  obtain ⟨Mo, hMo⟩ := exists_model Bs hBs W _ _ hV hX 1 one_ne_zero rfl
  obtain ⟨Mo', hMo'⟩ := exists_model Bs hBs W₁ _ _ hV' hX (-1) (neg_ne_zero.2 one_ne_zero) rfl
  obtain ⟨om, hom, htr⟩ := exists_weil Bs hBs true W X e _ _ hV hX 1 rfl (by rw [neg_gram, one_smul, neg_neg]) rfl Mo hMo hA
  obtain ⟨om', hom', htr'⟩ := exists_weil Bs hBs false W₁ X e _ _ hV' hX (-1) rfl (neg_one_smul _ _) rfl Mo' hMo' hB
  have hr := h.rank
  have hev := h.even
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  have hTe : (⟨α, β, T, ∅⟩ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E).T = T := by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars.T]
  refine ⟨Bs, ⟨p, q, _, _, _, Mo, Mo'⟩, ⟨α, β, T, ∅⟩, om, om',
    ⟨rfl, rfl, rfl, rfl, fun w => ⟨τf w, fun _ => rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, ⟨hBs, ?_, ?_, hom, hom'⟩, htr, htr',
    ⟨lV, lX⟩, ⟨lV', lX⟩, hTe, hT0, fun v => (hT1 v v.2).1.choose_spec⟩
  · refine ⟨by omega, hr ▸ hev, fun w => ?_, ?_, hn2, hV, hV', hX, hMo, hMo'⟩
    · have h1 := eα w
      have h3 := eβ w
      have h4 := hab (τf w)
      rw [hr] at h4
      have : (((W.rank + W₁.rank : ℕ) : ℤ) : ℚ) < ((mα w - mβ w : ℤ) : ℚ) := by
        push_cast at h4 ⊢
        rw [h1, h3]
        linarith
      exact_mod_cast this
    · obtain ⟨m, hm⟩ := hev
      show 2 * (p + q) + 1 < (W.rank - W₁.rank) / 2
      omega
  · refine ⟨h.hecA, h.hecB, GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resA),
      GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resB), hα, hβ, Finset.disjoint_empty_right _,
      hTe.le, fun w hw => hT2 w (hTe ▸ hw), fun w hw => (hT3 w fun h0 => hw ?_).1, fun w hw => (hT3 w fun h0 => hw ?_).2,
      ⟨hTe.symm ▸ hv₁, hv₁s⟩⟩
    · rw [hTe]; exact h0
    · rw [hTe]; exact h0
