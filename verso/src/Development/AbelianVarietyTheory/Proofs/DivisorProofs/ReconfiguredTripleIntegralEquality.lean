import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalingVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryLeviLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMultiplicativeStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConeRepresentatives
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatUOfForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsotropicVectorsTransitiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviRationalOfComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearCompositionAdaptedPlanesStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.MidLineParam

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, ← Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_skew' (hσ : ∀ e, σ (σ e) = e) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `h : (fun i => σ ((ι *ᵥ u') i)) = ι.map σ *ᵥ fun i => σ (u' i)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul]`. Rewrite using `[form, form, h, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc]`.
-/
theorem form_gram {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin m) E) (u u' : Fin m → E) :
    form σ J (ι *ᵥ u) (ι *ᵥ u') = form σ (ιᵀ * J * ι.map σ) u u' := by
  have h : (fun i => σ ((ι *ᵥ u') i)) = ι.map σ *ᵥ fun i => σ (u' i) := by
    funext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [form, form, h, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 k hk), rfl⟩`.
-/
theorem unit_of_inclR {k : E} (hk : k ≠ 0) : ∃ l : (AE F E)ˣ, l.1 = inclR (F := F) (AF F) k :=
  ⟨Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 k hk), rfl⟩

end GlobalTheory.MidLineParam

open GlobalTheory.MidLineParam GlobalTheory.PlaneLevi in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hTr hTr₁ V V' W₁' hTr₁' e W₂ H₂ i₀ i₁ hH₂ emb hemb w hw nn hnn T hT`. Use `haveI := nontrivial_AE (F := F) (E := E)`. Establish `hσ : ∀ z, σ (σ z) = z` using `invol_of_good hTr.base`. Establish `hH'` using `hC.hH'`. Establish `hsk : ∀ i j, σ (G.W.J j i) = -G.W.J i j` using `hTr.geo.hW.skew`.

Establish `hsk₁ : ∀ i j, σ (G₁.W.J j i) = -G₁.W.J i j` using `hTr₁.geo.hW.skew`. Establish `hdet₁ : G₁.W.J.det ≠ 0` using `GlobalTheory.UnipComm.det_ne_of_skew B G₁.W.J hTr₁.geo.hW.sig`. Take `⟨hdec, hιinj⟩` from `GlobalTheory.LeviRatHerm.decomp hTr.geo.hW.lat hH'`. Take `⟨hdec₂, -⟩` from `GlobalTheory.LeviRatHerm.decomp hTr₁'.geo.hW.lat hH₂`. Establish `hx₂x₂ : form σ G₁.W.J H₂.x H₂.x = 0` using `hH₂.xx`.

Establish `hy₂y₂ : form σ G₁.W.J H₂.y H₂.y = 0` using `hH₂.yy`. Establish `hx₂y₂ : form σ G₁.W.J H₂.x H₂.y = 1` using `hH₂.xy`. Establish `hyx : form σ G.W.J H'.y H'.x = -1` using `by rw [form_skew' hσ hsk, hH'.xy, map_one]`. Establish `hx0 : H'.x ≠ 0` using `fun h0 => by`. Use `hH'.xy` as an intermediate fact.

Rewrite `this` using `[h0]`. Simplify using `[form] at this`. Take `⟨T₁, hT₁⟩` from `GlobalTheory.ConeSmallCT.exists_isReps F E σ (a + b) G₁.W.J H₂.x`. Establish `hratg : ∀ (γ : UA σ G₁.W.J) (c : E), γ ∈ ratU σ G₁.W.J → w * nn (inclR (F` using `F) (AF F) c) * emb γ ∈ ratU σ G.W.J := fun γ c hγ => mul_mem (mul_mem hw.1 (GlobalTheory.T.shear_composition_adapted_planes F E σ _ _ _ G.W.J H' H₂ hdec hdec₂ nn hnn c)) (GlobalTheory.T.levi_rational_of_component F E σ _ _ G.W G₁.W H' hdec γ (emb γ) (hemb γ) hγ)`. Establish `hKg : ∀ (γ : UA σ G₁.W.J), γ ∈ ratU σ G₁.W.J → ∃ u : Fin (a + b) → E, mat γ⁻¹ *ᵥ incV F H₂.x = incV F u ∧ u ≠ 0 ∧ ∀ c : E, mat (w * nn (inclR (F` using `F) (AF F) c) * emb γ)⁻¹ *ᵥ incV F H'.x = incV F (H'.ι *ᵥ u + (-c) • H'.x) := by`.

Introduce `γ hγ`. Take `⟨Q, hQ, hQf⟩` from `rat_mulVec (inv_mem hγ)`. Use `⟨Q *ᵥ H₂.x, hQ _, fun h0 => ?_, fun c => ?_⟩` and prove the remaining obligations. Use `hQf H₂.x H₂.y` as an intermediate fact. Rewrite `this` using `[h0, hx₂y₂]`.

Simplify using `[form] at this`. Apply `mat_inv_mulVec` to reduce the goal to its premises. Establish `h1 : mat γ *ᵥ incV F (Q *ᵥ H₂.x) = incV F H₂.x`. Rewrite using `[← hQ, ← mat_mul_mulVec, mul_inv_cancel]`. Conclude with `Matrix.one_mulVec _`.

Establish `hl` using `hemb γ`. Establish `he1 : mat (emb γ) *ᵥ incV F H'.x = incV F H'.x` using `by rw [hl.1]; simp`. Establish `he2 : mat (emb γ) *ᵥ incV F (H'.ι *ᵥ (Q *ᵥ H₂.x)) = incV F (H'.ι *ᵥ H₂.x)`. Rewrite using `[← incM_mulVec, Matrix.mulVec_mulVec, hl.2.2, ← Matrix.mulVec_mulVec, h1, incM_mulVec]`. Establish `hs` using `(hnn (inclR (F := F) (AF F) c))`.

Rewrite using `[mat_mul_mulVec, mat_mul_mulVec, incV_add, incV_smul, Matrix.mulVec_add, Matrix.mulVec_smul, he1, he2, Matrix.mulVec_add, Matrix.mulVec_smul, hs.1, hs.2.1, map_neg, neg_smul, add_neg_cancel_right, hw.2.2.2.1]`. Set `R : UA σ G.W.J → T₁ × E → Prop` to `fun t p => GlobalTheory.ConeSmallSer.StabLn H'.x (w * nn (inclR (F := F) (AF F) p.2) * emb p.1.1 * t⁻¹)`. Establish `hRin : ∀ (g t : UA σ G.W.J) (q : Fin (a + (b + 2)) → E) (k : E), k ≠ 0 → mat g⁻¹ *ᵥ incV F H'.x = incV F q → mat t⁻¹ *ᵥ incV F H'.x = incV F (k • q) → GlobalTheory.ConeSmallSer.StabLn H'.x (g * t⁻¹)`. Introduce `g t q k hk hg ht`. Take `⟨l, hl⟩` from `unit_of_inclR (F := F) hk`.

Use `⟨l, ?_⟩` and prove the remaining obligations. Establish `hgq : mat g *ᵥ incV F q = incV F H'.x`. Rewrite using `[← hg, ← mat_mul_mulVec, mul_inv_cancel]`. Conclude with `Matrix.one_mulVec _`. Rewrite using `[mat_mul_mulVec, ht, incV_smul, Matrix.mulVec_smul, hgq, hl]`.

Establish `hRout : ∀ (g t : UA σ G.W.J) (q v : Fin (a + (b + 2)) → E), q ≠ 0 → mat g⁻¹ *ᵥ incV F H'.x = incV F q → mat t⁻¹ *ᵥ incV F H'.x = incV F v → GlobalTheory.ConeSmallSer.StabLn H'.x (g * t⁻¹) → ∃ k : E, k ≠ 0 ∧ v = k • q`. Introduce `g t q v hq hg ht hst`. Take `⟨l, hl⟩` from `hst`. Rewrite `hl` using `[mat_mul_mulVec, ht]`. Establish `h2 : incV F v = l.1 • incV F q`.

Rewrite using `[← mat_inv_mulVec g hl, Matrix.mulVec_smul, hg]`. Take `⟨k, hk, hv⟩` from `scal_rat hq h2`. Use `⟨k, fun h0 => ?_, hv⟩` and prove the remaining obligations. Rewrite `hk` using `[h0, map_zero]`. Conclude with `l.ne_zero hk`.

Establish `hq0 : ∀ (u : Fin (a + b) → E) (c : E), u ≠ 0 → H'.ι *ᵥ u + (-c) • H'.x ≠ 0`. Introduce `u c hu h0`. Establish `h1 : form σ G.W.J (H'.ι *ᵥ u + (-c) • H'.x) H'.y = -c`. Rewrite using `[form_add_left, form_smul_left, (hH'.orth u).2, hH'.xy]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hz : form σ G.W.J (0 : Fin (a + (b + 2)) → E) H'.y = 0` using `by simp [form]`. Rewrite `h1` using `[h0, hz]`. Establish `hc : c = 0` using `by linear_combination h1`. Rewrite `h0` using `[hc, neg_zero, zero_smul, add_zero]`. Conclude with `hu (hιinj u h0)`.

Establish `hfwdE : ∀ t ∈ GlobalTheory.ConeSmallSer.midSet H'.x T, ∃ p : T₁ × E, R t p`. Introduce `t ht`. Take `⟨Q, hQ, hQf⟩` from `rat_mulVec (inv_mem (hT.1 ht.1))`. Establish `hvx : form σ G.W.J (Q *ᵥ H'.x) H'.x = 0`. Establish `h` using `ht.2.2`.

Unfold `GlobalTheory.ConeSmallSer.OrthLn at h`. Rewrite `h` using `[hQ, incV_dot_form]`. Conclude with `inclR_injective (h.trans (map_zero _).symm)`. Take `⟨s, r, u, hsu⟩` from `hdec (Q *ᵥ H'.x)`. Establish `hr : r = 0`.

Establish `h` using `hvx`. Rewrite `h` using `[hsu, form_add_left, form_add_left, form_smul_left, form_smul_left, hH'.xx, (hH'.orth u).1, hyx]`. Take the linear combination `-h`. Rewrite `hsu` using `[hr, zero_smul, add_zero]`. Establish `hxu : form σ G.W.J H'.x (H'.ι *ᵥ u) = 0` using `by rw [form_skew' hσ hsk, (hH'.orth u).1, map_zero, neg_zero]`.

Establish `huu : form σ G₁.W.J u u = 0`. Establish `h1 : form σ G.W.J (Q *ᵥ H'.x) (Q *ᵥ H'.x) = 0` using `by rw [hQf, hH'.xx]`. Rewrite `h1` using `[hsu]`. Simplify using `only [form_add_left, form_add_right, form_smul_left, form_smul_right, hH'.xx, (hH'.orth u).1, hxu, form_gram, hH'.gram, mul_zero, add_zero, zero_add] at h1`. Conclude with `h1`.

Establish `hu0 : u ≠ 0`. Introduce `hu`. Rewrite `hsu` using `[hu, Matrix.mulVec_zero, add_zero]`. Establish `hs0 : s ≠ 0`. Introduce `hs`.

Establish `h1` using `hQf H'.x H'.y`. Rewrite `h1` using `[hsu, hs, zero_smul, hH'.xy]`. Simplify using `[form] at h1`. Apply `ht.2.1` to reduce the goal to its premises. Take `⟨l, hl⟩` from `unit_of_inclR (F := F) (inv_ne_zero hs0)`.

Use `⟨l, ?_⟩` and prove the remaining obligations. Establish `h1 : mat t⁻¹ *ᵥ incV F (s⁻¹ • H'.x) = incV F H'.x`. Rewrite using `[incV_smul, Matrix.mulVec_smul, hQ, hsu, incV_smul, smul_smul, ← map_mul, inv_mul_cancel₀ hs0, map_one, one_smul]`. Establish `h2` using `mat_inv_mulVec t⁻¹ h1`. Rewrite `h2` using `[inv_inv]`.

Rewrite using `[h2, incV_smul, hl]`. Take `⟨g₁, hg₁, μ, hμ, hg₁u⟩` from `GlobalTheory.T.rational_isotropic_vectors_transitive F E σ (a + b) G₁.W.J H₂.x H₂.y u hσ hsk₁ hdet₁ hx₂x₂ hy₂y₂ hx₂y₂ hu0 huu`. Take `⟨γ, ⟨hγT, l, hl⟩, -⟩` from `hT₁.2 g₁ hg₁`. Establish `hγ : γ ∈ ratU σ G₁.W.J` using `hT₁.1 hγT`. Take `⟨u', hu', hu'0, hK⟩` from `hKg γ hγ`.

Establish `h3 : mat g₁ *ᵥ incV F (μ⁻¹ • u) = incV F H₂.x`. Rewrite using `[incV_smul, Matrix.mulVec_smul, hg₁u, ← incV_smul, smul_smul, inv_mul_cancel₀ hμ, one_smul]`. Establish `h4 : mat g₁ *ᵥ incV F u' = l.1 • incV F H₂.x` using `by rw [← hu', ← mat_mul_mulVec, hl]`. Establish `h5 : incV F u' = l.1 • incV F (μ⁻¹ • u)`. Rewrite using `[← mat_inv_mulVec g₁ h4, Matrix.mulVec_smul, mat_inv_mulVec g₁ h3]`.

Take `⟨k, -, hk⟩` from `scal_rat (smul_ne_zero (inv_ne_zero hμ) hu0) h5`. Establish `hκ : u' = (k * μ⁻¹) • u` using `by rw [hk, smul_smul]`. Establish `hκ0 : k * μ⁻¹ ≠ 0`. Introduce `h0`. Rewrite `hκ` using `[h0, zero_smul]`.

Conclude with `hu'0 hκ`. Use `⟨(⟨γ, hγT⟩, -((k * μ⁻¹) * s)), ?_⟩` and prove the remaining obligations. Use `hRin _ t _ (k * μ⁻¹)⁻¹ (inv_ne_zero hκ0) (hK _) ?_` and prove the remaining obligations. Establish `hc1 : (k * μ⁻¹)⁻¹ * (k * μ⁻¹) = 1` using `inv_mul_cancel₀ hκ0`. Rewrite using `[hQ, hsu, hκ, Matrix.mulVec_smul, neg_neg, smul_add, smul_smul, smul_smul, hc1, ← mul_assoc, hc1, one_smul, one_mul, add_comm (s • H'.x)]`.

Establish `hbwdE : ∀ p : T₁ × E, ∃ t, t ∈ GlobalTheory.ConeSmallSer.midSet H'.x T ∧ R t p`. Introduce and unpack `⟨⟨γ, hγT⟩, c⟩`. Establish `hγ` using `hT₁.1 hγT`. Take `⟨u, hu, hu0, hK⟩` from `hKg γ hγ`. Take `⟨t, ⟨htT, l, hl⟩, -⟩` from `hT.2 _ (hratg γ c hγ)`.

Rewrite `hl` using `[mat_mul_mulVec]`. Establish `ht1 : mat t⁻¹ *ᵥ incV F H'.x = l.1 • incV F (H'.ι *ᵥ u + (-c) • H'.x)`. Rewrite using `[← hK c, ← Matrix.mulVec_smul, mat_inv_mulVec _ hl]`. Use `⟨t, ⟨htT, ?_, ?_⟩, ⟨l, by rw [mat_mul_mulVec]; exact hl⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨l₀, hl₀⟩`.

Establish `h1 : mat t⁻¹ *ᵥ incV F H'.x = (l₀⁻¹).1 • incV F H'.x`. Apply `mat_inv_mulVec` to reduce the goal to its premises. Rewrite using `[Matrix.mulVec_smul, hl₀, smul_smul, Units.inv_mul, one_smul]`. Rewrite `ht1` using `[h1]`. Establish `h2 : incV F (H'.ι *ᵥ u + (-c) • H'.x) = (l⁻¹ * l₀⁻¹).1 • incV F H'.x`.

Rewrite using `[Units.val_mul, mul_smul, ht1, smul_smul, Units.inv_mul, one_smul]`. Take `⟨k, -, hk⟩` from `scal_rat hx0 h2`. Establish `h3 : H'.ι *ᵥ u = (k + c) • H'.x`. Combine the equalities or inequalities in the displayed calculation. Establish `h4 : form σ G.W.J (H'.ι *ᵥ u) H'.y = 0` using `(hH'.orth u).2`.

Rewrite `h4` using `[h3, form_smul_left, hH'.xy, mul_one]`. Rewrite `h3` using `[h4, zero_smul]`. Conclude with `hu0 (hιinj u h3)`. Unfold `GlobalTheory.ConeSmallSer.OrthLn`. Rewrite using `[ht1, smul_dotProduct, incV_dot_form, form_add_left, form_smul_left, (hH'.orth u).1, hH'.xx, mul_zero, add_zero, map_zero, smul_zero]`.

Establish `hfwdU : ∀ t ∈ T, ∀ p p' : T₁ × E, R t p → R t p' → p = p'`. Introduce and unpack `t htT ⟨⟨γ, hγT⟩, c⟩ ⟨⟨γ', hγT'⟩, c'⟩ hp hp'`. Establish `hγ` using `hT₁.1 hγT`. Establish `hγ'` using `hT₁.1 hγT'`. Take `⟨Q, hQ, -⟩` from `rat_mulVec (inv_mem (hT.1 htT))`.

Take `⟨u, hu, hu0, hK⟩` from `hKg γ hγ`. Take `⟨u', hu', hu'0, hK'⟩` from `hKg γ' hγ'`. Take `⟨k, hk0, hk⟩` from `hRout _ t _ _ (hq0 u c hu0) (hK c) (hQ _) hp`. Take `⟨k', -, hk'⟩` from `hRout _ t _ _ (hq0 u' c' hu'0) (hK' c') (hQ _) hp'`. Establish `e1 : H'.ι *ᵥ u + (-c) • H'.x = (k⁻¹ * k') • (H'.ι *ᵥ u' + (-c') • H'.x)`.

Rewrite using `[← smul_smul, ← hk', hk, smul_smul, inv_mul_cancel₀ hk0, one_smul]`. Establish `ec : c = (k⁻¹ * k') * c'`. Establish `h` using `congrArg (fun z => form σ G.W.J z H'.y) e1`. Simplify using `only [form_add_left, form_smul_left, (hH'.orth _).2, hH'.xy] at h`. Take the linear combination `-h`.

Establish `e2 : H'.ι *ᵥ u = (k⁻¹ * k') • (H'.ι *ᵥ u')`. Establish `h` using `e1`. Rewrite `h` using `[smul_add, smul_smul, ec, show -((k⁻¹ * k') * c') = (k⁻¹ * k') * -c' by ring]`. Conclude with `add_right_cancel h`. Establish `eu : u = (k⁻¹ * k') • u'`.

Establish `h` using `hιinj (u - (k⁻¹ * k') • u') (by rw [Matrix.mulVec_sub, Matrix.mulVec_smul, e2, sub_self])`. Conclude with `sub_eq_zero.1 h`. Establish `hκ0 : k⁻¹ * k' ≠ 0`. Introduce `h0`. Rewrite `eu` using `[h0, zero_smul]`.

Conclude with `hu0 eu`. Establish `hγγ' : γ = γ'`. Take `⟨lκ, hlκ⟩` from `unit_of_inclR (F := F) hκ0`. Apply `(hT₁.2 γ' hγ').unique` to reduce the goal to its premises. Use `⟨hγT, lκ, ?_⟩` and prove the remaining obligations.

Rewrite using `[mat_mul_mulVec, hu, eu, incV_smul, Matrix.mulVec_smul, ← hu', ← mat_mul_mulVec, mul_inv_cancel, show mat (1 : UA σ G₁.W.J) = 1 from rfl, Matrix.one_mulVec, hlκ]`. Use `⟨hγT', 1, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv_cancel, show mat (1 : UA σ G₁.W.J) = 1 from rfl, Matrix.one_mulVec, Units.val_one, one_smul]`. Establish `huu' : u = u'`. Substitute `hγγ'` using the available equality.

Conclude with `incV_injective (F := F) (hu.symm.trans hu')`. Establish `hκ1 : k⁻¹ * k' = 1`. Establish `h : (k⁻¹ * k' - 1) • u' = 0` using `by rw [sub_smul, one_smul, ← eu, huu', sub_self]`. Break down `smul_eq_zero.1 h with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h`.

Conclude with `absurd h hu'0`. Rewrite `ec` using `[hκ1, one_mul]`. Substitute `hγγ'` using the available equality. Rewrite using `[ec]`. Establish `hbwdU : ∀ t t' : UA σ G.W.J, t ∈ T → t' ∈ T → ∀ p : T₁ × E, R t p → R t' p → t = t'`.

Introduce `t t' ht ht' p h h'`. Conclude with `(hT.2 _ (hratg p.1.1 p.2 (hT₁.1 p.1.2))).unique ⟨ht, h⟩ ⟨ht', h'⟩`. Establish `hex : ∀ t : GlobalTheory.ConeSmallSer.midSet H'.x T, ∃ p, R t.1 p` using `fun t => hfwdE t.1 t.2`. Use `choose f hf using hex`. Establish `hinj : Function.Injective f` using `fun t t' h => Subtype.ext (hbwdU t.1 t'.1 t.2.1 t'.2.1 (f t) (hf t) (by rw [h]; exact hf t'))`.

Establish `hsurj : Function.Surjective f` using `fun p => by`. Take `⟨t, ht, hR⟩` from `hbwdE p`. Conclude with `⟨⟨t, ht⟩, hfwdU t ht.1 _ _ (hf ⟨t, ht⟩) hR⟩`. Conclude with `⟨T₁, hT₁.1, Equiv.ofBijective f ⟨hinj, hsurj⟩, fun t => hf t⟩`.
-/
theorem GlobalTheory.MidLineParam.midSet_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' →
    ∀ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ →
    ∀ emb : UA σ G₁.W.J → UA σ G.W.J, (∀ h₁, IsLevi H' 1 h₁ (emb h₁)) →
    ∀ w : UA σ G.W.J, IsSwap H' H₂ w → ∀ nn : AE F E → UA σ G.W.J, IsShear H' H₂ nn →
    ∀ T : Set (UA σ G.W.J), GlobalTheory.ConeSmallCT.IsReps T H'.x →
    ∃ T₁ : Set (UA σ G₁.W.J), T₁ ⊆ ratU σ G₁.W.J ∧ ∃ ε : GlobalTheory.ConeSmallSer.midSet H'.x T ≃ T₁ × E, ∀ t,
      GlobalTheory.ConeSmallSer.StabLn H'.x (w * nn (inclR (F := F) (AF F) (ε t).2) * emb (ε t).1.1 * t.1⁻¹) := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hTr hTr₁ V V' W₁' hTr₁' e W₂ H₂ i₀ i₁ hH₂ emb hemb w hw nn hnn T hT
  haveI := nontrivial_AE (F := F) (E := E)
  have hσ : ∀ z, σ (σ z) = z := invol_of_good hTr.base
  have hH' := hC.hH'
  have hsk : ∀ i j, σ (G.W.J j i) = -G.W.J i j := hTr.geo.hW.skew
  have hsk₁ : ∀ i j, σ (G₁.W.J j i) = -G₁.W.J i j := hTr₁.geo.hW.skew
  have hdet₁ : G₁.W.J.det ≠ 0 := GlobalTheory.UnipComm.det_ne_of_skew B G₁.W.J hTr₁.geo.hW.sig
  obtain ⟨hdec, hιinj⟩ := GlobalTheory.LeviRatHerm.decomp hTr.geo.hW.lat hH'
  obtain ⟨hdec₂, -⟩ := GlobalTheory.LeviRatHerm.decomp hTr₁'.geo.hW.lat hH₂
  have hx₂x₂ : form σ G₁.W.J H₂.x H₂.x = 0 := hH₂.xx
  have hy₂y₂ : form σ G₁.W.J H₂.y H₂.y = 0 := hH₂.yy
  have hx₂y₂ : form σ G₁.W.J H₂.x H₂.y = 1 := hH₂.xy
  have hyx : form σ G.W.J H'.y H'.x = -1 := by rw [form_skew' hσ hsk, hH'.xy, map_one]
  have hx0 : H'.x ≠ 0 := fun h0 => by
    have := hH'.xy; rw [h0] at this; simp [form] at this

  obtain ⟨T₁, hT₁⟩ := GlobalTheory.ConeSmallCT.exists_isReps F E σ (a + b) G₁.W.J H₂.x

  have hratg : ∀ (γ : UA σ G₁.W.J) (c : E), γ ∈ ratU σ G₁.W.J →
      w * nn (inclR (F := F) (AF F) c) * emb γ ∈ ratU σ G.W.J := fun γ c hγ =>
    mul_mem (mul_mem hw.1 (GlobalTheory.T.shear_composition_adapted_planes F E σ _ _ _ G.W.J H' H₂ hdec hdec₂ nn hnn c))
      (GlobalTheory.T.levi_rational_of_component F E σ _ _ G.W G₁.W H' hdec γ (emb γ) (hemb γ) hγ)

  have hKg : ∀ (γ : UA σ G₁.W.J), γ ∈ ratU σ G₁.W.J → ∃ u : Fin (a + b) → E,
      mat γ⁻¹ *ᵥ incV F H₂.x = incV F u ∧ u ≠ 0 ∧ ∀ c : E,
      mat (w * nn (inclR (F := F) (AF F) c) * emb γ)⁻¹ *ᵥ incV F H'.x = incV F (H'.ι *ᵥ u + (-c) • H'.x) := by
    intro γ hγ
    obtain ⟨Q, hQ, hQf⟩ := rat_mulVec (inv_mem hγ)
    refine ⟨Q *ᵥ H₂.x, hQ _, fun h0 => ?_, fun c => ?_⟩
    · have := hQf H₂.x H₂.y
      rw [h0, hx₂y₂] at this; simp [form] at this
    · apply mat_inv_mulVec
      have h1 : mat γ *ᵥ incV F (Q *ᵥ H₂.x) = incV F H₂.x := by
        rw [← hQ, ← mat_mul_mulVec, mul_inv_cancel]; exact Matrix.one_mulVec _
      have hl := hemb γ
      have he1 : mat (emb γ) *ᵥ incV F H'.x = incV F H'.x := by rw [hl.1]; simp
      have he2 : mat (emb γ) *ᵥ incV F (H'.ι *ᵥ (Q *ᵥ H₂.x)) = incV F (H'.ι *ᵥ H₂.x) := by
        rw [← incM_mulVec, Matrix.mulVec_mulVec, hl.2.2, ← Matrix.mulVec_mulVec, h1, incM_mulVec]
      have hs := (hnn (inclR (F := F) (AF F) c))
      rw [mat_mul_mulVec, mat_mul_mulVec, incV_add, incV_smul, Matrix.mulVec_add, Matrix.mulVec_smul, he1, he2,
        Matrix.mulVec_add, Matrix.mulVec_smul, hs.1, hs.2.1, map_neg, neg_smul, add_neg_cancel_right, hw.2.2.2.1]

  let R : UA σ G.W.J → T₁ × E → Prop := fun t p =>
    GlobalTheory.ConeSmallSer.StabLn H'.x (w * nn (inclR (F := F) (AF F) p.2) * emb p.1.1 * t⁻¹)
  have hRin : ∀ (g t : UA σ G.W.J) (q : Fin (a + (b + 2)) → E) (k : E), k ≠ 0 → mat g⁻¹ *ᵥ incV F H'.x = incV F q →
      mat t⁻¹ *ᵥ incV F H'.x = incV F (k • q) → GlobalTheory.ConeSmallSer.StabLn H'.x (g * t⁻¹) := by
    intro g t q k hk hg ht
    obtain ⟨l, hl⟩ := unit_of_inclR (F := F) hk
    refine ⟨l, ?_⟩
    have hgq : mat g *ᵥ incV F q = incV F H'.x := by
      rw [← hg, ← mat_mul_mulVec, mul_inv_cancel]; exact Matrix.one_mulVec _
    rw [mat_mul_mulVec, ht, incV_smul, Matrix.mulVec_smul, hgq, hl]
  have hRout : ∀ (g t : UA σ G.W.J) (q v : Fin (a + (b + 2)) → E), q ≠ 0 → mat g⁻¹ *ᵥ incV F H'.x = incV F q →
      mat t⁻¹ *ᵥ incV F H'.x = incV F v → GlobalTheory.ConeSmallSer.StabLn H'.x (g * t⁻¹) → ∃ k : E, k ≠ 0 ∧ v = k • q := by
    intro g t q v hq hg ht hst
    obtain ⟨l, hl⟩ := hst
    rw [mat_mul_mulVec, ht] at hl
    have h2 : incV F v = l.1 • incV F q := by
      rw [← mat_inv_mulVec g hl, Matrix.mulVec_smul, hg]
    obtain ⟨k, hk, hv⟩ := scal_rat hq h2
    refine ⟨k, fun h0 => ?_, hv⟩
    rw [h0, map_zero] at hk; exact l.ne_zero hk
  have hq0 : ∀ (u : Fin (a + b) → E) (c : E), u ≠ 0 → H'.ι *ᵥ u + (-c) • H'.x ≠ 0 := by
    intro u c hu h0
    have h1 : form σ G.W.J (H'.ι *ᵥ u + (-c) • H'.x) H'.y = -c := by
      rw [form_add_left, form_smul_left, (hH'.orth u).2, hH'.xy]; ring
    have hz : form σ G.W.J (0 : Fin (a + (b + 2)) → E) H'.y = 0 := by simp [form]
    rw [h0, hz] at h1
    have hc : c = 0 := by linear_combination h1
    rw [hc, neg_zero, zero_smul, add_zero] at h0
    exact hu (hιinj u h0)

  have hfwdE : ∀ t ∈ GlobalTheory.ConeSmallSer.midSet H'.x T, ∃ p : T₁ × E, R t p := by
    intro t ht
    obtain ⟨Q, hQ, hQf⟩ := rat_mulVec (inv_mem (hT.1 ht.1))
    have hvx : form σ G.W.J (Q *ᵥ H'.x) H'.x = 0 := by
      have h := ht.2.2
      unfold GlobalTheory.ConeSmallSer.OrthLn at h
      rw [hQ, incV_dot_form] at h
      exact inclR_injective (h.trans (map_zero _).symm)
    obtain ⟨s, r, u, hsu⟩ := hdec (Q *ᵥ H'.x)
    have hr : r = 0 := by
      have h := hvx
      rw [hsu, form_add_left, form_add_left, form_smul_left, form_smul_left, hH'.xx, (hH'.orth u).1, hyx] at h
      linear_combination -h
    rw [hr, zero_smul, add_zero] at hsu
    have hxu : form σ G.W.J H'.x (H'.ι *ᵥ u) = 0 := by rw [form_skew' hσ hsk, (hH'.orth u).1, map_zero, neg_zero]
    have huu : form σ G₁.W.J u u = 0 := by
      have h1 : form σ G.W.J (Q *ᵥ H'.x) (Q *ᵥ H'.x) = 0 := by rw [hQf, hH'.xx]
      rw [hsu] at h1
      simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, hH'.xx, (hH'.orth u).1, hxu,
        form_gram, hH'.gram, mul_zero, add_zero, zero_add] at h1
      exact h1
    have hu0 : u ≠ 0 := by
      intro hu
      rw [hu, Matrix.mulVec_zero, add_zero] at hsu
      have hs0 : s ≠ 0 := by
        intro hs
        have h1 := hQf H'.x H'.y
        rw [hsu, hs, zero_smul, hH'.xy] at h1
        simp [form] at h1
      apply ht.2.1
      obtain ⟨l, hl⟩ := unit_of_inclR (F := F) (inv_ne_zero hs0)
      refine ⟨l, ?_⟩
      have h1 : mat t⁻¹ *ᵥ incV F (s⁻¹ • H'.x) = incV F H'.x := by
        rw [incV_smul, Matrix.mulVec_smul, hQ, hsu, incV_smul, smul_smul, ← map_mul, inv_mul_cancel₀ hs0, map_one,
          one_smul]
      have h2 := mat_inv_mulVec t⁻¹ h1
      rw [inv_inv] at h2
      rw [h2, incV_smul, hl]
    obtain ⟨g₁, hg₁, μ, hμ, hg₁u⟩ :=
      GlobalTheory.T.rational_isotropic_vectors_transitive F E σ (a + b) G₁.W.J H₂.x H₂.y u hσ hsk₁ hdet₁ hx₂x₂ hy₂y₂ hx₂y₂ hu0 huu
    obtain ⟨γ, ⟨hγT, l, hl⟩, -⟩ := hT₁.2 g₁ hg₁
    have hγ : γ ∈ ratU σ G₁.W.J := hT₁.1 hγT
    obtain ⟨u', hu', hu'0, hK⟩ := hKg γ hγ
    have h3 : mat g₁ *ᵥ incV F (μ⁻¹ • u) = incV F H₂.x := by
      rw [incV_smul, Matrix.mulVec_smul, hg₁u, ← incV_smul, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    have h4 : mat g₁ *ᵥ incV F u' = l.1 • incV F H₂.x := by rw [← hu', ← mat_mul_mulVec, hl]
    have h5 : incV F u' = l.1 • incV F (μ⁻¹ • u) := by
      rw [← mat_inv_mulVec g₁ h4, Matrix.mulVec_smul, mat_inv_mulVec g₁ h3]
    obtain ⟨k, -, hk⟩ := scal_rat (smul_ne_zero (inv_ne_zero hμ) hu0) h5
    have hκ : u' = (k * μ⁻¹) • u := by rw [hk, smul_smul]
    have hκ0 : k * μ⁻¹ ≠ 0 := by
      intro h0; rw [h0, zero_smul] at hκ; exact hu'0 hκ
    refine ⟨(⟨γ, hγT⟩, -((k * μ⁻¹) * s)), ?_⟩
    refine hRin _ t _ (k * μ⁻¹)⁻¹ (inv_ne_zero hκ0) (hK _) ?_
    have hc1 : (k * μ⁻¹)⁻¹ * (k * μ⁻¹) = 1 := inv_mul_cancel₀ hκ0
    rw [hQ, hsu, hκ, Matrix.mulVec_smul, neg_neg, smul_add, smul_smul, smul_smul, hc1, ← mul_assoc, hc1, one_smul,
      one_mul, add_comm (s • H'.x)]

  have hbwdE : ∀ p : T₁ × E, ∃ t, t ∈ GlobalTheory.ConeSmallSer.midSet H'.x T ∧ R t p := by
    rintro ⟨⟨γ, hγT⟩, c⟩
    have hγ := hT₁.1 hγT
    obtain ⟨u, hu, hu0, hK⟩ := hKg γ hγ
    obtain ⟨t, ⟨htT, l, hl⟩, -⟩ := hT.2 _ (hratg γ c hγ)
    rw [mat_mul_mulVec] at hl
    have ht1 : mat t⁻¹ *ᵥ incV F H'.x = l.1 • incV F (H'.ι *ᵥ u + (-c) • H'.x) := by
      rw [← hK c, ← Matrix.mulVec_smul, mat_inv_mulVec _ hl]
    refine ⟨t, ⟨htT, ?_, ?_⟩, ⟨l, by rw [mat_mul_mulVec]; exact hl⟩⟩
    · rintro ⟨l₀, hl₀⟩
      have h1 : mat t⁻¹ *ᵥ incV F H'.x = (l₀⁻¹).1 • incV F H'.x := by
        apply mat_inv_mulVec
        rw [Matrix.mulVec_smul, hl₀, smul_smul, Units.inv_mul, one_smul]
      rw [h1] at ht1
      have h2 : incV F (H'.ι *ᵥ u + (-c) • H'.x) = (l⁻¹ * l₀⁻¹).1 • incV F H'.x := by
        rw [Units.val_mul, mul_smul, ht1, smul_smul, Units.inv_mul, one_smul]
      obtain ⟨k, -, hk⟩ := scal_rat hx0 h2
      have h3 : H'.ι *ᵥ u = (k + c) • H'.x := by
        calc H'.ι *ᵥ u = (H'.ι *ᵥ u + (-c) • H'.x) + c • H'.x := by rw [neg_smul]; abel
          _ = (k + c) • H'.x := by rw [hk, add_smul]
      have h4 : form σ G.W.J (H'.ι *ᵥ u) H'.y = 0 := (hH'.orth u).2
      rw [h3, form_smul_left, hH'.xy, mul_one] at h4
      rw [h4, zero_smul] at h3
      exact hu0 (hιinj u h3)
    · unfold GlobalTheory.ConeSmallSer.OrthLn
      rw [ht1, smul_dotProduct, incV_dot_form, form_add_left, form_smul_left, (hH'.orth u).1, hH'.xx, mul_zero,
        add_zero, map_zero, smul_zero]

  have hfwdU : ∀ t ∈ T, ∀ p p' : T₁ × E, R t p → R t p' → p = p' := by
    rintro t htT ⟨⟨γ, hγT⟩, c⟩ ⟨⟨γ', hγT'⟩, c'⟩ hp hp'
    have hγ := hT₁.1 hγT
    have hγ' := hT₁.1 hγT'
    obtain ⟨Q, hQ, -⟩ := rat_mulVec (inv_mem (hT.1 htT))
    obtain ⟨u, hu, hu0, hK⟩ := hKg γ hγ
    obtain ⟨u', hu', hu'0, hK'⟩ := hKg γ' hγ'
    obtain ⟨k, hk0, hk⟩ := hRout _ t _ _ (hq0 u c hu0) (hK c) (hQ _) hp
    obtain ⟨k', -, hk'⟩ := hRout _ t _ _ (hq0 u' c' hu'0) (hK' c') (hQ _) hp'
    have e1 : H'.ι *ᵥ u + (-c) • H'.x = (k⁻¹ * k') • (H'.ι *ᵥ u' + (-c') • H'.x) := by
      rw [← smul_smul, ← hk', hk, smul_smul, inv_mul_cancel₀ hk0, one_smul]
    have ec : c = (k⁻¹ * k') * c' := by
      have h := congrArg (fun z => form σ G.W.J z H'.y) e1
      simp only [form_add_left, form_smul_left, (hH'.orth _).2, hH'.xy] at h
      linear_combination -h
    have e2 : H'.ι *ᵥ u = (k⁻¹ * k') • (H'.ι *ᵥ u') := by
      have h := e1
      rw [smul_add, smul_smul, ec, show -((k⁻¹ * k') * c') = (k⁻¹ * k') * -c' by ring] at h
      exact add_right_cancel h
    have eu : u = (k⁻¹ * k') • u' := by
      have h := hιinj (u - (k⁻¹ * k') • u') (by rw [Matrix.mulVec_sub, Matrix.mulVec_smul, e2, sub_self])
      exact sub_eq_zero.1 h
    have hκ0 : k⁻¹ * k' ≠ 0 := by
      intro h0; rw [h0, zero_smul] at eu; exact hu0 eu
    have hγγ' : γ = γ' := by
      obtain ⟨lκ, hlκ⟩ := unit_of_inclR (F := F) hκ0
      apply (hT₁.2 γ' hγ').unique
      · refine ⟨hγT, lκ, ?_⟩
        rw [mat_mul_mulVec, hu, eu, incV_smul, Matrix.mulVec_smul, ← hu', ← mat_mul_mulVec, mul_inv_cancel,
          show mat (1 : UA σ G₁.W.J) = 1 from rfl, Matrix.one_mulVec, hlκ]
      · refine ⟨hγT', 1, ?_⟩
        rw [mul_inv_cancel, show mat (1 : UA σ G₁.W.J) = 1 from rfl, Matrix.one_mulVec, Units.val_one, one_smul]
    have huu' : u = u' := by
      subst hγγ'; exact incV_injective (F := F) (hu.symm.trans hu')
    have hκ1 : k⁻¹ * k' = 1 := by
      have h : (k⁻¹ * k' - 1) • u' = 0 := by rw [sub_smul, one_smul, ← eu, huu', sub_self]
      rcases smul_eq_zero.1 h with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h hu'0
    rw [hκ1, one_mul] at ec
    subst hγγ'
    rw [ec]

  have hbwdU : ∀ t t' : UA σ G.W.J, t ∈ T → t' ∈ T → ∀ p : T₁ × E, R t p → R t' p → t = t' := by
    intro t t' ht ht' p h h'
    exact (hT.2 _ (hratg p.1.1 p.2 (hT₁.1 p.1.2))).unique ⟨ht, h⟩ ⟨ht', h'⟩
  have hex : ∀ t : GlobalTheory.ConeSmallSer.midSet H'.x T, ∃ p, R t.1 p := fun t => hfwdE t.1 t.2
  choose f hf using hex
  have hinj : Function.Injective f := fun t t' h =>
    Subtype.ext (hbwdU t.1 t'.1 t.2.1 t'.2.1 (f t) (hf t) (by rw [h]; exact hf t'))
  have hsurj : Function.Surjective f := fun p => by
    obtain ⟨t, ht, hR⟩ := hbwdE p
    exact ⟨⟨t, ht⟩, hfwdU t ht.1 _ _ (hf ⟨t, ht⟩) hR⟩
  exact ⟨T₁, hT₁.1, Equiv.ofBijective f ⟨hinj, hsurj⟩, fun t => hf t⟩

end
