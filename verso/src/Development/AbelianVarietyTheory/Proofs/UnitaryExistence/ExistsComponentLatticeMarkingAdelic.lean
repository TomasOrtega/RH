import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionSelfDualOfSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLinearApproxTower
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralTmulOneMulMemAdelicCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SelfDualLatticeOccurs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGramStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOneStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceFormStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvarianceStatement

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.Occ

open GlobalTheory.AdLat GlobalTheory.AdLat.Half
open scoped nonZeroDivisors

/- English proof (translation)
Establish `back : ∀ w ∈ hat F (L : Set (Fin n → E)), ∀ y ∈ L, hermA c G w (fv F y) ∈ hat1 F (J : Set E)`. Introduce `w hw y hy`. Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨t, ht, x, hx, rfl⟩` from `hw`.

Rewrite using `[hermA_tmul_fv]`. Conclude with `AddSubgroup.subset_closure ⟨t, ht, _, hL x hx y hy, rfl⟩`. Consider the case `zero`. Establish `: hermA c G 0 (fv F y) = 0` using `by simp [hermA]`. Rewrite using `[this]`.

Conclude with `zero_mem _`. Consider the case `add w w' _ _ h h' => rw [hermA_add_left]`. Conclude with `add_mem h h'`. Consider the case `neg w _ h => rw [hermA_neg_left]`. Conclude with `neg_mem h`.

Establish `both : ∀ u ∈ hat F (L : Set (Fin n → E)), ∀ v ∈ hat F (L : Set (Fin n → E)), hermA c G u v ∈ hat1 F (J : Set E)` using `fun u hu v hv => herm_mem_of_fv c G _ _ _ (back u hu) v hv`. Establish `hMs : ∀ x : Fin n → RA F E, N • x = (N : RA F E) • x` using `fun x => (Nat.cast_smul_eq_nsmul _ _ _).symm`. Establish `hsM : sg (FiniteAdeleRing (𝓞 F) F) c (N : RA F E) = N` using `map_natCast _ N`. Establish `hfx` using `fv_mem_hat' (F := F) (L : Set (Fin n → E)) x hx`. Establish `hfy` using `fv_mem_hat' (F := F) (L : Set (Fin n → E)) y hy`.

Establish `hu : hermA c G w (fv F y + N • w') + hermA c G (fv F x) w' ∈ hat1 F (J : Set E)` using `add_mem (both _ hw _ (add_mem hfy (nsmul_mem hw' N))) (both _ hfx _ hw')`. Establish `e1 : hermA c G (fv F x') (fv F y') - hermA c G (fv F x) (fv F y) = (N : RA F E) * (hermA c G w (fv F y + N • w') + hermA c G (fv F x) w')`. Rewrite using `[ex, ey, hg, Half.herm_add_left, hMs w, Half.herm_smul_left, Half.herm_add_right c G (fv F x), hMs w', Half.herm_smul_right, hsM]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∀ x y : Fin n → E, hermA c G (fv F x) (fv F y) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (∑ a, ∑ b, x a * G a b * c (y b))` using `fun x y => hermA_tmul_fv c G 1 x y`.

Rewrite `e1` using `[e2, e2, ← TensorProduct.tmul_sub]`. Use `set d := (∑ a, ∑ b, x' a * G a b * c (y' b)) - (∑ a, ∑ b, x a * G a b * c (y b)) with hd`. Establish `hN' : (N : E) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hNt : (N : RA F E) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E)` using `(map_natCast (Algebra.TensorProduct.includeRight : E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E) N).symm`. Use `⟨(N : E)⁻¹ * d, ((adelicCompletion_fractionalIdeal_properties F E).2.1 J _).1 ?_, by rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul]⟩` and prove the remaining obligations.

Establish `e3 : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((N : E)⁻¹ * d) : RA F E) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E)⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] d)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite using `[e3, e1, hNt, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hN', ← Algebra.TensorProduct.one_def, one_mul]`. Conclude with `hu`.
-/
theorem form_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (J : FractionalIdeal (𝓞 E)⁰ E) (g : Matrix (Fin n) (Fin n) (RA F E))
    (hL : ∀ x ∈ L, ∀ y ∈ L, (∑ a, ∑ b, x a * G a b * c (y b)) ∈ J)
    (hg : ∀ x y, hermA c G (g *ᵥ x) (g *ᵥ y) = hermA c G x y) {N : ℕ} (hN : 0 < N)
    {x y x' y' : Fin n → E} (hx : x ∈ L) (hy : y ∈ L) {w w' : Fin n → RA F E}
    (hw : w ∈ hat F (L : Set (Fin n → E))) (hw' : w' ∈ hat F (L : Set (Fin n → E)))
    (ex : fv F x' = g *ᵥ (fv F x + N • w)) (ey : fv F y' = g *ᵥ (fv F y + N • w')) :
    ∃ z ∈ J, (∑ a, ∑ b, x' a * G a b * c (y' b)) - (∑ a, ∑ b, x a * G a b * c (y b)) = N * z := by
  have back : ∀ w ∈ hat F (L : Set (Fin n → E)), ∀ y ∈ L,
      hermA c G w (fv F y) ∈ hat1 F (J : Set E) := by
    intro w hw y hy
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hw
      rw [hermA_tmul_fv]
      exact AddSubgroup.subset_closure ⟨t, ht, _, hL x hx y hy, rfl⟩
    | zero =>
      have : hermA c G 0 (fv F y) = 0 := by simp [hermA]
      rw [this]; exact zero_mem _
    | add w w' _ _ h h' => rw [hermA_add_left]; exact add_mem h h'
    | neg w _ h => rw [hermA_neg_left]; exact neg_mem h
  have both : ∀ u ∈ hat F (L : Set (Fin n → E)), ∀ v ∈ hat F (L : Set (Fin n → E)),
      hermA c G u v ∈ hat1 F (J : Set E) := fun u hu v hv => herm_mem_of_fv c G _ _ _ (back u hu) v hv
  have hMs : ∀ x : Fin n → RA F E, N • x = (N : RA F E) • x := fun x =>
    (Nat.cast_smul_eq_nsmul _ _ _).symm
  have hsM : sg (FiniteAdeleRing (𝓞 F) F) c (N : RA F E) = N := map_natCast _ N
  have hfx := fv_mem_hat' (F := F) (L : Set (Fin n → E)) x hx
  have hfy := fv_mem_hat' (F := F) (L : Set (Fin n → E)) y hy
  have hu : hermA c G w (fv F y + N • w') + hermA c G (fv F x) w' ∈ hat1 F (J : Set E) :=
    add_mem (both _ hw _ (add_mem hfy (nsmul_mem hw' N))) (both _ hfx _ hw')
  have e1 : hermA c G (fv F x') (fv F y') - hermA c G (fv F x) (fv F y) =
      (N : RA F E) * (hermA c G w (fv F y + N • w') + hermA c G (fv F x) w') := by
    rw [ex, ey, hg, Half.herm_add_left, hMs w, Half.herm_smul_left, Half.herm_add_right c G (fv F x), hMs w',
      Half.herm_smul_right, hsM]
    ring
  have e2 : ∀ x y : Fin n → E, hermA c G (fv F x) (fv F y) =
      (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (∑ a, ∑ b, x a * G a b * c (y b)) :=
    fun x y => hermA_tmul_fv c G 1 x y
  rw [e2, e2, ← TensorProduct.tmul_sub] at e1
  set d := (∑ a, ∑ b, x' a * G a b * c (y' b)) - (∑ a, ∑ b, x a * G a b * c (y b)) with hd
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (N : RA F E) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E) :=
    (map_natCast (Algebra.TensorProduct.includeRight :
      E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E) N).symm
  refine ⟨(N : E)⁻¹ * d, ((adelicCompletion_fractionalIdeal_properties F E).2.1 J _).1 ?_, by rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul]⟩
  have e3 : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((N : E)⁻¹ * d) : RA F E) =
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E)⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] d) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [e3, e1, hNt, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hN',
    ← Algebra.TensorProduct.one_def, one_mul]
  exact hu

/- English proof (translation)
Simplify using `[herm]`.
-/
theorem herm_neg' {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : herm (-G) x y = -∑ a, ∑ b, x a * G a b * cc (y b) := by
  simp [herm]

/- English proof (translation)
Establish `h1 : cc (herm G x y) = herm G y x`. Unfold `herm`. Unfold `cc at *`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [map_sum, map_mul, hG, IsCMField.complexConj_apply_apply]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) (ξ * herm G x y)`. Rewrite using `[← h2, ← h1]`. Use `congr 1`.

Unfold `cc at *`. Express the relevant statement in the definitionally equal form `_ = IsCMField.complexConj E _`. Rewrite using `[map_mul, hξ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trace_swap {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ a b, cc (G a b) = G b a) (ξ : E) (hξ : cc ξ = -ξ) (x y : Fin n → E) :
    Algebra.trace ℚ E (ξ * -herm G y x) = Algebra.trace ℚ E (ξ * herm G x y) := by
  have h1 : cc (herm G x y) = herm G y x := by
    unfold herm
    unfold cc at *
    rw [Finset.sum_comm]
    simp only [map_sum, map_mul, hG, IsCMField.complexConj_apply_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have h2 := Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) (ξ * herm G x y)
  rw [← h2, ← h1]
  congr 1
  unfold cc at *
  change _ = IsCMField.complexConj E _
  rw [map_mul, hξ]
  ring

/- English proof (translation)
Rewrite `e` using `[e', Matrix.mulVec_mulVec, Tower.fv_add, Tower.fv_nsmul, Matrix.mulVec_add, Tower.mulVec_nsmul]`. Rewrite using `[smul_sub, sub_eq_sub_iff_add_eq_add, ← e, add_comm]`.
-/
theorem mark_congr {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (RA F E)) {N : ℕ} {x x' t w : Fin n → E} {w' : Fin n → RA F E}
    (e : A *ᵥ fv F x' = fv F (t + N • w)) (e' : fv F x' = B *ᵥ (fv F x + N • w')) :
    fv F t - (A * B) *ᵥ fv F x = N • ((A * B) *ᵥ w' - fv F w) := by
  rw [e', Matrix.mulVec_mulVec, Tower.fv_add, Tower.fv_nsmul, Matrix.mulVec_add, Tower.mulVec_nsmul] at e
  rw [smul_sub, sub_eq_sub_iff_add_eq_add, ← e, add_comm]

end GlobalTheory.Member.Occ

open GlobalTheory.Member.Occ GlobalTheory.AdLat in

/- English proof (translation)
Introduce `D H Dw l Xo c σ V r C hC h`. Take `⟨hr, g, e, F, M, ι, θ, x₀⟩` from `C`. Substitute `hr` using the available equality. Take `⟨⟨-, -, ⟨hinj, hrange⟩, hisom⟩, -, hA, hgood, hbase, hW, -, -⟩` from `hC`. Simplify using `only at hinj hrange hisom hbase hW`.

Take `⟨-, hfv, -, -, -, hcc, -, hGc, hGdet, hT, -⟩` from `GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V`. Take `⟨hfg1, hsp1, -⟩` from `GlobalTheory.T.adelicElementLattice_full_and_completion D V 1`. Take `⟨hfg, hsp, hlat, -⟩` from `GlobalTheory.T.adelicElementLattice_full_and_completion D V h`. Take `⟨hJ, hsd1, -⟩` from `GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V 1 _ rfl`. Take `⟨-, -, hsd⟩` from `GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V h _ rfl`.

Take `⟨f, hf1, hf2, hf3⟩` from `GlobalTheory.AdLat.exists_linear_approx_tower D.host.F D.host.E V.rank (latG V 1) (finHom V h) (latG V h) hfg1 hsp1 hlat`. Set `ε : Dw.La ≃ₗ[𝓞 D.host.E] latG V 1` to `(LinearEquiv.ofInjective ι hinj).trans (LinearEquiv.ofEq _ _ hrange)`. Establish `hε : ∀ a, (ε a : Fin V.rank → D.host.E) = ι a` using `fun a => rfl`. Establish `hk : ∀ k, (M.X k).Gm = -V.gramᵀ ∧ (M.X k).ξ0 = -D.host.xi0` using `fun k => by`. Take `⟨h1, h2⟩` from `hW k`.

Conclude with `⟨by rw [h1]; rfl, h2⟩`. Establish `hξ : cc D.host.xi0 = -D.host.xi0`. Establish `h` using `(M.X ⟨0, F.n_pos⟩).ξ0_im`. Rewrite `h` using `[(hk _).2]`. Unfold `cc at h ⊢`.

Rewrite `h` using `[map_neg]`. Conclude with `neg_injective h`. Establish `hG' : ∀ a b, cc ((-V.gramᵀ) a b) = (-V.gramᵀ) b a` using `fun a b => by`. Rewrite using `[← hcc, Matrix.neg_apply, Matrix.neg_apply, map_neg, hGc]`. Establish `hEF : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) (ι x) (ι y))` using `fun x y => by`.

Rewrite using `[hisom, hT, trace_swap _ hG' _ hξ, neg_neg]`. Take `⟨k, γ', hu, hl, hm⟩` from `GlobalTheory.selfDual_lattice_occurs GlobalTheory.QNorm.hasseNormSt D.host.E H Dw l Xo _ g _ F V.rank M (-D.host.xi0) (-V.gramᵀ) ι (latG V h) (fun N => f N ∘ₗ ε.toLinearMap) hA hgood ((GlobalTheory.Relab.relab_good D.host.E H l c σ hgood).2.2.2 Dw g e) hbase hk ⟨hinj, by rw [← Li …`. Rewrite using `[Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hGdet, hEF⟩ hfg hsp hsd`. Use the proof step `(fun n m hn hm a => hf2 n m hn hm (ε a))`. Use the proof step `(fun n hn => ⟨fun a => ((hf3 n hn).1 (ε a)).trans ⟨fun ⟨v, hv⟩ => ⟨ε.symm v, ε.injective (by rw [hv, map_nsmul, ε.apply_symm_apply])⟩, fun ⟨v, hv⟩ => ⟨ε v, by rw [hv, map_nsmul]⟩⟩, fun a' => by`.

Take `⟨a, v, hv⟩` from `(hf3 n hn).2 a'`. Conclude with `⟨ε.symm a, v, by simpa using hv⟩⟩)`. Use the proof step `(fun n hn a a' => by`. Take `⟨w, hw, ew⟩` from `hf1 n hn (ε a)`. Take `⟨w', hw', ew'⟩` from `hf1 n hn (ε a')`.

Take `⟨z, hz, ez⟩` from `form_congr (latG V 1) (cF D) V.gramᵀ _ _ (fun x hx => (hsd1 x).2 hx) (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V h).1 hn (ε a).2 (ε a').2 hw hw' ew ew'`. Take `⟨t, ht⟩` from `(hJ z).1 hz 1`. Use `⟨-t, ?_⟩` and prove the remaining obligations. Simplify using `only [hcc, hε] at ez`. Rewrite using `[hEF, ← map_sub, ← mul_sub, herm_neg', herm_neg', neg_sub_neg, ← neg_sub]`.

Use `erw [ez]`. Establish `: -(-D.host.xi0) * -((n : D.host.E) * z) = (-(n : ℚ)) • (D.host.xi0 * (((1 : 𝓞 D.host.E) : D.host.E) * z))`. Simplify using `[Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, map_smul, ht]`.

Use the proof step `simp)`. Take `⟨hQ, -, hex, -, hfin⟩` from `GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V`. Take `⟨γ, hγ⟩` from `hex γ' hu`. Take `⟨hmv, -⟩` from `(GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).1 γ γ' h hγ`. Take `⟨-, -, -, hhat1, hhat2, -⟩` from `GlobalTheory.T.adelicElementLattice_full_and_completion D V (γ * h)`.

Establish `hΛ : ∀ v, v ∈ (M.X k).Λ ↔ v ∈ latG V (γ * h)` using `fun v => by`. Establish `e : v = γ'.val *ᵥ ((γ'⁻¹).val *ᵥ v)`. Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Rewrite using `[e, ← hl, ← hmv]`. Use `⟨k, γ, (hQ γ).2 ⟨γ', hγ⟩, ?_, fun a ha => ?_⟩` and prove the remaining obligations.

Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Conclude with `⟨v, (hΛ v).1 hv, rfl⟩`. Introduce and unpack `⟨v, hv, rfl⟩`.

Conclude with `(hΛ v).2 hv`. Take `⟨w, hw, ew⟩` from `hm a ha`. Take `⟨w', hw', ew'⟩` from `hf1 l.M (lt_of_lt_of_le (by norm_num) l.three_le) (ε a)`. Establish `m1 : (finHom V (γ * h)).1 *ᵥ w' ∈ latGHat V (γ * h)`. Rewrite using `[← SetLike.mem_coe, hhat1]`.

Conclude with `⟨w', hw', rfl⟩`. Establish `m2 : fv D.host.F w ∈ latGHat V (γ * h)`. Rewrite using `[hhat2]`. Conclude with `Half.fv_mem_hat' _ _ ((hΛ w).1 hw)`. Use `⟨_, sub_mem m1 m2, ?_⟩` and prove the remaining obligations.

Establish `e1` using `(hfin γ γ' hγ).1 (f l.M (ε a))`. Establish `ew2 : γ'.val *ᵥ (f l.M (ε a) : Fin V.rank → D.host.E) = (M.φ k (F.t k a) : Fin V.rank → D.host.E) + l.M • w` using `ew`. Rewrite `e1` using `[ew2]`. Establish `e2` using `mark_congr (finHom V γ).1 (finHom V h).1 e1 ew'`. Rewrite `e2` using `[← Units.val_mul, ← map_mul]`.

Conclude with `e2`.
-/
theorem GlobalTheory.Member.exists_mark : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h : GA D V, ∃ k γ, C.Mark h k γ := by
  intro D H Dw l Xo c σ V r C hC h
  obtain ⟨hr, g, e, F, M, ι, θ, x₀⟩ := C
  subst hr
  obtain ⟨⟨-, -, ⟨hinj, hrange⟩, hisom⟩, -, hA, hgood, hbase, hW, -, -⟩ := hC
  dsimp only at hinj hrange hisom hbase hW
  obtain ⟨-, hfv, -, -, -, hcc, -, hGc, hGdet, hT, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  obtain ⟨hfg1, hsp1, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V 1
  obtain ⟨hfg, hsp, hlat, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V h
  obtain ⟨hJ, hsd1, -⟩ := GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V 1 _ rfl
  obtain ⟨-, -, hsd⟩ := GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V h _ rfl
  obtain ⟨f, hf1, hf2, hf3⟩ := GlobalTheory.AdLat.exists_linear_approx_tower D.host.F D.host.E V.rank (latG V 1)
    (finHom V h) (latG V h) hfg1 hsp1 hlat
  let ε : Dw.La ≃ₗ[𝓞 D.host.E] latG V 1 :=
    (LinearEquiv.ofInjective ι hinj).trans (LinearEquiv.ofEq _ _ hrange)
  have hε : ∀ a, (ε a : Fin V.rank → D.host.E) = ι a := fun a => rfl
  have hk : ∀ k, (M.X k).Gm = -V.gramᵀ ∧ (M.X k).ξ0 = -D.host.xi0 := fun k => by
    obtain ⟨h1, h2⟩ := hW k
    exact ⟨by rw [h1]; rfl, h2⟩
  have hξ : cc D.host.xi0 = -D.host.xi0 := by
    have h := (M.X ⟨0, F.n_pos⟩).ξ0_im
    rw [(hk _).2] at h
    unfold cc at h ⊢
    rw [map_neg] at h
    exact neg_injective h
  have hG' : ∀ a b, cc ((-V.gramᵀ) a b) = (-V.gramᵀ) b a := fun a b => by
    rw [← hcc, Matrix.neg_apply, Matrix.neg_apply, map_neg, hGc]
  have hEF : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) (ι x) (ι y)) := fun x y => by
    rw [hisom, hT, trace_swap _ hG' _ hξ, neg_neg]
  obtain ⟨k, γ', hu, hl, hm⟩ := GlobalTheory.selfDual_lattice_occurs GlobalTheory.QNorm.hasseNormSt D.host.E H Dw l Xo _ g _ F V.rank M
    (-D.host.xi0) (-V.gramᵀ) ι (latG V h) (fun N => f N ∘ₗ ε.toLinearMap) hA hgood
    ((GlobalTheory.Relab.relab_good D.host.E H l c σ hgood).2.2.2 Dw g e) hbase hk
    ⟨hinj, by rw [← LinearMap.coe_range, hrange]; exact hsp1, hG', by
      rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hGdet, hEF⟩ hfg hsp hsd
    (fun n m hn hm a => hf2 n m hn hm (ε a))
    (fun n hn => ⟨fun a => ((hf3 n hn).1 (ε a)).trans
      ⟨fun ⟨v, hv⟩ => ⟨ε.symm v, ε.injective (by rw [hv, map_nsmul, ε.apply_symm_apply])⟩,
        fun ⟨v, hv⟩ => ⟨ε v, by rw [hv, map_nsmul]⟩⟩, fun a' => by
      obtain ⟨a, v, hv⟩ := (hf3 n hn).2 a'
      exact ⟨ε.symm a, v, by simpa using hv⟩⟩)
    (fun n hn a a' => by
      obtain ⟨w, hw, ew⟩ := hf1 n hn (ε a)
      obtain ⟨w', hw', ew'⟩ := hf1 n hn (ε a')
      obtain ⟨z, hz, ez⟩ := form_congr (latG V 1) (cF D) V.gramᵀ _ _
        (fun x hx => (hsd1 x).2 hx) (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V h).1 hn (ε a).2 (ε a').2 hw hw' ew ew'
      obtain ⟨t, ht⟩ := (hJ z).1 hz 1
      refine ⟨-t, ?_⟩
      simp only [hcc, hε] at ez
      rw [hEF, ← map_sub, ← mul_sub, herm_neg', herm_neg', neg_sub_neg, ← neg_sub]
      erw [ez]
      have : -(-D.host.xi0) * -((n : D.host.E) * z) =
          (-(n : ℚ)) • (D.host.xi0 * (((1 : 𝓞 D.host.E) : D.host.E) * z)) := by
        simp [Algebra.smul_def]; ring
      rw [this, map_smul, ht]
      simp)
  obtain ⟨hQ, -, hex, -, hfin⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨γ, hγ⟩ := hex γ' hu
  obtain ⟨hmv, -⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).1 γ γ' h hγ
  obtain ⟨-, -, -, hhat1, hhat2, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V (γ * h)
  have hΛ : ∀ v, v ∈ (M.X k).Λ ↔ v ∈ latG V (γ * h) := fun v => by
    have e : v = γ'.val *ᵥ ((γ'⁻¹).val *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [e, ← hl, ← hmv]
  refine ⟨k, γ, (hQ γ).2 ⟨γ', hγ⟩, ?_, fun a ha => ?_⟩
  · ext v
    constructor
    · intro hv
      exact ⟨v, (hΛ v).1 hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact (hΛ v).2 hv
  · obtain ⟨w, hw, ew⟩ := hm a ha
    obtain ⟨w', hw', ew'⟩ := hf1 l.M (lt_of_lt_of_le (by norm_num) l.three_le) (ε a)
    have m1 : (finHom V (γ * h)).1 *ᵥ w' ∈ latGHat V (γ * h) := by
      rw [← SetLike.mem_coe, hhat1]
      exact ⟨w', hw', rfl⟩
    have m2 : fv D.host.F w ∈ latGHat V (γ * h) := by
      rw [hhat2]
      exact Half.fv_mem_hat' _ _ ((hΛ w).1 hw)
    refine ⟨_, sub_mem m1 m2, ?_⟩
    have e1 := (hfin γ γ' hγ).1 (f l.M (ε a))
    have ew2 : γ'.val *ᵥ (f l.M (ε a) : Fin V.rank → D.host.E) =
        (M.φ k (F.t k a) : Fin V.rank → D.host.E) + l.M • w := ew
    rw [ew2] at e1
    have e2 := mark_congr (finHom V γ).1 (finHom V h).1 e1 ew'
    rw [← Units.val_mul, ← map_mul] at e2
    exact e2
