import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExistenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReconfiguredTriplePlaneIntegralStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.ConeSmallMidJB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use extensionality with `φ`. Simplify using `only [Model.SoLoc, Model.IsLinBar, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, ι, ⟨hb, ht, hm⟩, h3⟩`. Conclude with `⟨h1, ι, ⟨hb, ht, hm⟩, h3⟩`.

Introduce and unpack `⟨h1, ι, ⟨hb, ht, hm⟩, h3⟩`. Conclude with `⟨h1, ι, ⟨hb, ht, hm⟩, h3⟩`.
-/
theorem soLoc_reG {B : Base F E} {a b : ℕ} {G₁ : Geo σ a b} {V : Spc F E a} {V' : Spc F E b} {W₁' : Spc F E (a + b)}
    {v₁ : Pl F} (t : E →ₐ[F] Fv F v₁) :
    (reG G₁ V V' W₁').M'.SoLoc B.ψ t = G₁.M'.SoLoc B.ψ t := by
  ext φ
  simp only [Model.SoLoc, Model.IsLinBar, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, ι, ⟨hb, ht, hm⟩, h3⟩
    exact ⟨h1, ι, ⟨hb, ht, hm⟩, h3⟩
  · rintro ⟨h1, ι, ⟨hb, ht, hm⟩, h3⟩
    exact ⟨h1, ι, ⟨hb, ht, hm⟩, h3⟩

/- English proof (translation)
Unfold `Model.So`. Rewrite using `[soLoc_reG]`. Both sides reduce to the same expression.
-/
theorem so_reG {B : Base F E} {a b : ℕ} {G₁ : Geo σ a b} {V : Spc F E a} {V' : Spc F E b} {W₁' : Spc F E (a + b)} :
    (reG G₁ V V' W₁').M'.So B.ψ B.τ₁ = G₁.M'.So B.ψ B.τ₁ := by
  unfold Model.So
  rw [soLoc_reG]
  rfl

/- English proof (translation)
Introduce `t t' m m' hm hm' h`. Establish `cp : ∀ (s : (AE F E)ˣ) (y : ℝ), ((((absE F E s : ℝ) ^ y : ℝ)) : ℂ) = ((absE F E s : ℝ) : ℂ) ^ (y : ℂ)` using `fun s y => Complex.ofReal_cpow (NNReal.coe_nonneg _) _`. Establish `a2` using `ha t' m' hm' h`. Establish `a3` using `ha t m hm h`. Establish `b2` using `hb t' m' hm' h`.

Establish `b3` using `hb t m hm h`. Establish `a4` using `ha t' m' hm' (m * h)`. Establish `b4` using `hb t' m' hm' (m * h)`. Simplify using `only [cp] at a2 a3 b2 b3 a4 b4`. Simplify using `only [Pi.add_apply]`.

Rewrite using `[a4, b4, a2, b2, a3, b3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jrel_of_hasLaw {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {χ χ' : Chr F E} {z z' : ℝ}
    {fa fb : UA σ W.J → ℂ} (ha : HasLaw W₁ H' χ z fa) (hb : HasLaw W₁ H' χ' z' fb) :
    GlobalTheory.ConeSmallMid.JRel W₁ H' χ (z : ℂ) χ' (z' : ℂ) (fa + fb) := by
  intro t t' m m' hm hm' h
  have cp : ∀ (s : (AE F E)ˣ) (y : ℝ), ((((absE F E s : ℝ) ^ y : ℝ)) : ℂ) = ((absE F E s : ℝ) : ℂ) ^ (y : ℂ) :=
    fun s y => Complex.ofReal_cpow (NNReal.coe_nonneg _) _
  have a2 := ha t' m' hm' h
  have a3 := ha t m hm h
  have b2 := hb t' m' hm' h
  have b3 := hb t m hm h
  have a4 := ha t' m' hm' (m * h)
  have b4 := hb t' m' hm' (m * h)
  simp only [cp] at a2 a3 b2 b3 a4 b4
  simp only [Pi.add_apply]
  rw [a4, b4, a2, b2, a3, b3]
  ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨jrel_of_hasLaw ha hb, add_comm fb fa ▸ jrel_of_hasLaw hb ha⟩`.
-/
theorem jrel_both_of_hasLaw {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {χ χ' : Chr F E} {z z' : ℝ}
    {fa fb : UA σ W.J → ℂ} (ha : HasLaw W₁ H' χ z fa) (hb : HasLaw W₁ H' χ' z' fb) :
    GlobalTheory.ConeSmallMid.JRel W₁ H' χ (z : ℂ) χ' (z' : ℂ) (fa + fb) ∧
      GlobalTheory.ConeSmallMid.JRel W₁ H' χ' (z' : ℂ) χ (z : ℂ) (fa + fb) :=
  ⟨jrel_of_hasLaw ha hb, add_comm fb fa ▸ jrel_of_hasLaw hb ha⟩

/- English proof (translation)
Take `⟨-, h2⟩` from `GlobalTheory.T.split_existence hKP F E σ B a b (reG G₁ V V' W₁') X om₁ om₁' hT' e W₂ H₂ i₀ i₁ hH`. Take `⟨⟨fa, fb⟩, ⟨hct, hla, hlb⟩, -⟩` from `h2 Ψ (by rw [so_reG (G₁ := G₁) (V := V) (V' := V') (W₁' := W₁')]; exact hΨ)`. Establish `hj` using `jrel_both_of_hasLaw hla hlb`. Establish `cb : ((((b : ℝ) / 2 : ℝ)) : ℂ) = ((b : ℕ) : ℂ) / 2` using `by push_cast; ring`. Establish `ca : ((((a : ℝ) / 2 : ℝ)) : ℂ) = ((a : ℕ) : ℂ) / 2` using `by push_cast; ring`.

Rewrite `hj` using `[cb, ca]`. Conclude with `⟨fa + fb, hct, hj⟩`.
-/
theorem jb_pol (hKP : GlobalTheory.ThK.KP) {B : Base F E} {a b : ℕ} {G₁ : Geo σ a b} {X : Chars F E} {om₁ : Rep σ G₁.V G₁.W}
    {om₁' : Rep σ G₁.V' G₁.W} {V : Spc F E a} {V' : Spc F E b} {W₁' : Spc F E (a + b)}
    (hT' : IsTriple B (reG G₁ V V' W₁') X om₁ om₁') {e : ℕ} {W₂ : Spc F E e} {H₂ : Plane E (a + b) e} {i₀ i₁ : ℕ}
    (hH : H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁) (Ψ : Fn F b (a + b))
    (hΨ : Ψ ∈ PolData B (reG G₁ V V' W₁').M' ⊓ G₁.M'.So B.ψ B.τ₁) :
    ∃ c : UA σ G₁.W.J → ℂ, IsCT H₂ (G₁.M'.I om₁' Ψ) c ∧
      GlobalTheory.ConeSmallMid.JRel W₂ H₂ X.α (((b : ℕ) : ℂ) / 2) X.β (((a : ℕ) : ℂ) / 2) c ∧
      GlobalTheory.ConeSmallMid.JRel W₂ H₂ X.β (((a : ℕ) : ℂ) / 2) X.α (((b : ℕ) : ℂ) / 2) c := by
  obtain ⟨-, h2⟩ := GlobalTheory.T.split_existence hKP F E σ B a b (reG G₁ V V' W₁') X om₁ om₁' hT' e W₂ H₂ i₀ i₁ hH
  obtain ⟨⟨fa, fb⟩, ⟨hct, hla, hlb⟩, -⟩ := h2 Ψ (by rw [so_reG (G₁ := G₁) (V := V) (V' := V') (W₁' := W₁')]; exact hΨ)
  have hj := jrel_both_of_hasLaw hla hlb
  have cb : ((((b : ℝ) / 2 : ℝ)) : ℂ) = ((b : ℕ) : ℂ) / 2 := by push_cast; ring
  have ca : ((((a : ℝ) / 2 : ℝ)) : ℂ) = ((a : ℕ) : ℂ) / 2 := by push_cast; ring
  rw [cb, ca] at hj
  exact ⟨fa + fb, hct, hj⟩

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a b G₁ X om₁ om₁' hT V V' W₁' hT' e W₂ H₂ i₀ i₁ hH Ψ hΨ`. Take `⟨Ψs, hΨs, hconv⟩` from `GlobalTheory.T.reconfigured_triple_plane_integral hKP F E σ B a b G₁ X om₁ om₁' hT V V' W₁' hT' e W₂ H₂ i₀ i₁ hH Ψ hΨ`. Distinguish the cases in `hex : ∃ (μ : Measure (unip σ G₁.W H₂)) (𝓕 : Set (unip σ G₁.W H₂)), μ.IsHaarMeasure ∧ IsFundamentalDomain ((ratU σ G₁.W.J).subgroupOf (unip σ G₁.W H₂)) 𝓕 μ ∧ μ 𝓕 = 1`. Take `⟨μ₀, 𝓕₀, hμ₀, hF₀, h1₀⟩` from `hex choose cs hcs using fun k => jb_pol hKP hT' hH (Ψs k) (hΨs k) set c : UA σ G₁.W.J → ℂ := fun h => ∫ u in 𝓕₀, G₁.M'.I om₁' Ψ (u.1 * h) ∂μ₀ with hc`. Establish `hlim : ∀ h, Tendsto (fun k => cs k h) atTop (𝓝 (c h))`.

Introduce `h`. Establish `e1 : (fun k => cs k h) = fun k => ∫ u in 𝓕₀, G₁.M'.I om₁' (Ψs k) (u.1 * h) ∂μ₀`. Use function extensionality and compare the values at `fun k => (hcs k).1 μ₀ 𝓕₀ hμ₀ hF₀ h1₀ h`. Rewrite using `[e1]`. Conclude with `hconv μ₀ 𝓕₀ hμ₀ hF₀ h1₀ h`.

Establish `hJ : ∀ (χ : Chr F E) (z : ℂ) (χ' : Chr F E) (z' : ℂ), (∀ k, GlobalTheory.ConeSmallMid.JRel W₂ H₂ χ z χ' z' (cs k)) → GlobalTheory.ConeSmallMid.JRel W₂ H₂ χ z χ' z' c`. Introduce `χ z χ' z' hk t t' m m' hm hm' h`. Establish `T` using `((((hlim (m' * (m * h))).sub ((hlim (m * h)).const_mul ((χ' t' : ℂ) * ((absE F E t' : ℝ) : ℂ) ^ z'))).sub ((hlim (m' * h)).const_mul ((χ t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ z))).add ((hlim h).const_mul ((χ t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ z * ((χ' t' : ℂ) * ((absE F E t' : ℝ) : ℂ) …`. Establish `e0 : (fun k => cs k (m' * (m * h)) - (χ' t' : ℂ) * ((absE F E t' : ℝ) : ℂ) ^ z' * cs k (m * h) - (χ t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ z * cs k (m' * h) + (χ t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ z * ((χ' t' : ℂ) * ((absE F E t' : ℝ) : ℂ) ^ z') * cs k h) = fun _ => 0`. Use function extensionality and compare the values at `fun k => hk k t t' m m' hm hm' h`.

Rewrite `T` using `[e0]`. Conclude with `tendsto_nhds_unique T tendsto_const_nhds`. Use `⟨c, ?_, hJ _ _ _ _ fun k => (hcs k).2.1, hJ _ _ _ _ fun k => (hcs k).2.2⟩` and prove the remaining obligations. Introduce `μ 𝓕 hμ hF h1 h`. Establish `e1 : (fun k => cs k h) = fun k => ∫ u in 𝓕, G₁.M'.I om₁' (Ψs k) (u.1 * h) ∂μ`.

Use function extensionality and compare the values at `fun k => (hcs k).1 μ 𝓕 hμ hF h1 h`. Establish `T` using `hconv μ 𝓕 hμ hF h1 h`. Rewrite `T` using `[← e1]`. Conclude with `tendsto_nhds_unique (hlim h) T`. Use `⟨0, ?_, fun _ _ _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ => by simp⟩` and prove the remaining obligations.

Introduce `μ 𝓕 hμ hF h1`. Conclude with `absurd ⟨μ, 𝓕, hμ, hF, h1⟩ hex`.
-/
theorem jb_datum : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G₁ : Geo σ a b) (X : Chars F E) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G₁ X om₁ om₁' →
    ∀ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' →
    ∀ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ →
    ∀ Ψ ∈ G₁.M'.So B.ψ B.τ₁, ∃ c : UA σ G₁.W.J → ℂ, IsCT H₂ (G₁.M'.I om₁' Ψ) c ∧
      GlobalTheory.ConeSmallMid.JRel W₂ H₂ X.α (((b : ℕ) : ℂ) / 2) X.β (((a : ℕ) : ℂ) / 2) c ∧
      GlobalTheory.ConeSmallMid.JRel W₂ H₂ X.β (((a : ℕ) : ℂ) / 2) X.α (((b : ℕ) : ℂ) / 2) c := by
  intro hKP F E _ _ _ _ _ σ B a b G₁ X om₁ om₁' hT V V' W₁' hT' e W₂ H₂ i₀ i₁ hH Ψ hΨ
  obtain ⟨Ψs, hΨs, hconv⟩ := GlobalTheory.T.reconfigured_triple_plane_integral hKP F E σ B a b G₁ X om₁ om₁' hT V V' W₁' hT' e W₂ H₂ i₀ i₁ hH Ψ hΨ
  by_cases hex : ∃ (μ : Measure (unip σ G₁.W H₂)) (𝓕 : Set (unip σ G₁.W H₂)), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ G₁.W.J).subgroupOf (unip σ G₁.W H₂)) 𝓕 μ ∧ μ 𝓕 = 1
  · obtain ⟨μ₀, 𝓕₀, hμ₀, hF₀, h1₀⟩ := hex
    choose cs hcs using fun k => jb_pol hKP hT' hH (Ψs k) (hΨs k)
    set c : UA σ G₁.W.J → ℂ := fun h => ∫ u in 𝓕₀, G₁.M'.I om₁' Ψ (u.1 * h) ∂μ₀ with hc
    have hlim : ∀ h, Tendsto (fun k => cs k h) atTop (𝓝 (c h)) := by
      intro h
      have e1 : (fun k => cs k h) = fun k => ∫ u in 𝓕₀, G₁.M'.I om₁' (Ψs k) (u.1 * h) ∂μ₀ :=
        funext fun k => (hcs k).1 μ₀ 𝓕₀ hμ₀ hF₀ h1₀ h
      rw [e1]
      exact hconv μ₀ 𝓕₀ hμ₀ hF₀ h1₀ h
    have hJ : ∀ (χ : Chr F E) (z : ℂ) (χ' : Chr F E) (z' : ℂ),
        (∀ k, GlobalTheory.ConeSmallMid.JRel W₂ H₂ χ z χ' z' (cs k)) → GlobalTheory.ConeSmallMid.JRel W₂ H₂ χ z χ' z' c := by
      intro χ z χ' z' hk t t' m m' hm hm' h
      have T := ((((hlim (m' * (m * h))).sub ((hlim (m * h)).const_mul ((χ' t' : ℂ) * ((absE F E t' : ℝ) : ℂ) ^ z'))).sub
        ((hlim (m' * h)).const_mul ((χ t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ z))).add
        ((hlim h).const_mul ((χ t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ z * ((χ' t' : ℂ) * ((absE F E t' : ℝ) : ℂ) ^ z'))))
      have e0 : (fun k => cs k (m' * (m * h)) - (χ' t' : ℂ) * ((absE F E t' : ℝ) : ℂ) ^ z' * cs k (m * h) -
          (χ t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ z * cs k (m' * h) +
          (χ t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ z * ((χ' t' : ℂ) * ((absE F E t' : ℝ) : ℂ) ^ z') * cs k h) = fun _ => 0 :=
        funext fun k => hk k t t' m m' hm hm' h
      rw [e0] at T
      exact tendsto_nhds_unique T tendsto_const_nhds
    refine ⟨c, ?_, hJ _ _ _ _ fun k => (hcs k).2.1, hJ _ _ _ _ fun k => (hcs k).2.2⟩
    intro μ 𝓕 hμ hF h1 h
    have e1 : (fun k => cs k h) = fun k => ∫ u in 𝓕, G₁.M'.I om₁' (Ψs k) (u.1 * h) ∂μ :=
      funext fun k => (hcs k).1 μ 𝓕 hμ hF h1 h
    have T := hconv μ 𝓕 hμ hF h1 h
    rw [← e1] at T
    exact tendsto_nhds_unique (hlim h) T
  · refine ⟨0, ?_, fun _ _ _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ => by simp⟩
    intro μ 𝓕 hμ hF h1
    exact absurd ⟨μ, 𝓕, hμ, hF, h1⟩ hex

end GlobalTheory.ConeSmallMidJB
end
