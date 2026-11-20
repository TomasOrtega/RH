import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUpdate
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDerivativePolynomialFockArchimedeanUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleFiniteMapsForallPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxThetaVanishingFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommuteIsomSmul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

noncomputable section

open scoped Classical

namespace GlobalTheory.ThKLocSSW

open GlobalTheory.ThKLocSS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `hP` using `GlobalTheory.ThK.Inhab.pairV' hT`. Establish `hA` using `GlobalTheory.T.theta_action_exists hK.base`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hdetX : G.V'.J.det ≠ 0`. Introduce `h0`.

Apply `GlobalTheory.CartanLines.det_ne_zero_of_cartan (hP.herm.cartan w)` to reduce the goal to its premises. Rewrite using `[show G.V'.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix G.V'.J from rfl, ← RingHom.map_det, h0, map_zero]`. Establish `hdetW : G.W.J.det ≠ 0`. Introduce `h0`. Apply `GlobalTheory.CartanLines.det_ne_zero_of_cartan (hP.skew.cartan w)` to reduce the goal to its premises.

Rewrite using `[Matrix.det_smul, show G.W.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix G.W.J from rfl, ← RingHom.map_det, h0, map_zero, mul_zero]`. Establish `hL` using `GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ hP.base.cm a' (a + a') G.V' G.W G.M' B.ψ X.α (X.α / X.β) om' hP.base.std hP.herm.herm hdetX hP.skew.skew hdetW hP.resX hP.resW hP.hX hP.hW hP.weil B.emb hP.herm.cartan hP.skew.cartan γ hγ`. Establish `h1 : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v)`. Introduce `u _`. Use `show u • (mat (1 : UA σ G.V'.J) - 1) = 0`.

Establish `: mat (1 : UA σ G.V'.J) = 1` using `rfl`. Rewrite using `[this, sub_self, smul_zero]`. Establish `hpd : ∀ f f₁ : SInf F (Fin a' × Fin (a + a')), ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f f₁ → ∀ φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) → IsLineDer om' γ (pure f φ) (pure f₁ φ)`. Introduce `f f₁ hf φ hSB hev x`. Establish `hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1` using `(hev.and hP.good.std).mono fun w hw => hw.1.trans hw.2`.

Conclude with `hf _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd) x`. Introduce `Ψ hΨ`. Proceed by induction on `hΨ using Submodule.span_induction with`. Consider the case `mem Ψ hΨ`. Take `⟨f, hf, φ, hSB, hev, rfl⟩` from `hΨ`.

Take `⟨f₁, hf₁⟩` from `(hL f hf).1`. Use `⟨pure f₁ φ, hpd f f₁ hf₁ φ hSB hev, fun h hh => ?_⟩` and prove the remaining obligations. Establish `hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1` using `(hev.and hP.good.std).mono fun w hw => hw.1.trans hw.2`. Take `⟨φ₁, ⟨hφ₁, hact⟩, -⟩` from `(hA F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP v).1 1 h1 h hh (φ v) (hSB v)`. Establish `hmap : ∀ g : SInf F (Fin a' × Fin (a + a')), om' (1, h) (pure g φ) = pure g (Function.update φ v φ₁)`.

Introduce `g`. Take `⟨ρ, hρ, hρt⟩` from `GlobalTheory.PureFactor.exists_rest_factor v g φ hstd`. Establish `hpure : tens (evFin F v) (φ v) ρ = pure g φ` using `by rw [hρt, Function.update_eq_self]`. Establish `hRest : Rest (evFin F v) (φ v) ρ` using `⟨hρ, by rw [hpure]; exact GlobalTheory.TensUniq.pure_mem_schA g φ hSB hstd⟩`. Rewrite using `[← hpure, hact ρ hRest, hρt]`.

Establish `hSB' : ∀ w, Function.update φ v φ₁ w ∈ SB _`. Introduce `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[Function.update_self]`.

Conclude with `hφ₁`. Rewrite using `[Function.update_of_ne hw]`. Conclude with `hSB w`. Establish `hev' : ∀ᶠ w in Filter.cofinite, Function.update φ v φ₁ w = G.M'.vac w` using `by filter_upwards [hev, Filter.eventually_cofinite_ne v] with w hw hne`. Rewrite using `[Function.update_of_ne hne]`.

Conclude with `hw`. Rewrite using `[hmap f, hmap f₁]`. Conclude with `hpd f f₁ hf₁ _ hSB' hev'`. Consider the case `zero`. Use `⟨0, isLineDer_zero om' γ, fun h _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_zero]`. Conclude with `isLineDer_zero om' γ`. Consider the case `add x y _ _ hx hy`. Take `⟨x₁, hdx, hhx⟩` from `hx`. Take `⟨y₁, hdy, hhy⟩` from `hy`.

Use `⟨x₁ + y₁, isLineDer_add om' γ hdx hdy, fun h hh => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add]`. Conclude with `isLineDer_add om' γ (hhx h hh) (hhy h hh)`. Consider the case `smul c x _ hx`. Take `⟨x₁, hdx, hhx⟩` from `hx`.

Use `⟨c • x₁, isLineDer_smul om' γ c hdx, fun h hh => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, map_smul]`. Conclude with `isLineDer_smul om' γ c (hhx h hh)`.
-/
theorem exists_lineDer_polData' (hK : KP) {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') (v : Pl F)
    {γ : Multiplicative ℝ →* UA σ G.W.J} (hγ : γ ∈ Lines σ G.W) :
    ∀ Ψ ∈ PolData B G.M', ∃ Ψ₁, IsLineDer om' γ Ψ Ψ₁ ∧
      ∀ h ∈ UAt σ G.W (evFin F v), IsLineDer om' γ (om' (1, h) Ψ) (om' (1, h) Ψ₁) := by
  have hP := GlobalTheory.ThK.Inhab.pairV' hT
  have hA := GlobalTheory.T.theta_action_exists hK.base
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdetX : G.V'.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.CartanLines.det_ne_zero_of_cartan (hP.herm.cartan w)
    rw [show G.V'.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix G.V'.J from rfl, ← RingHom.map_det, h0, map_zero]
  have hdetW : G.W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.CartanLines.det_ne_zero_of_cartan (hP.skew.cartan w)
    rw [Matrix.det_smul, show G.W.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix G.W.J from rfl, ← RingHom.map_det, h0,
      map_zero, mul_zero]
  have hL := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ hP.base.cm a' (a + a') G.V' G.W G.M' B.ψ X.α (X.α / X.β) om' hP.base.std hP.herm.herm hdetX
    hP.skew.skew hdetW hP.resX hP.resW hP.hX hP.hW hP.weil B.emb hP.herm.cartan hP.skew.cartan γ hγ
  have h1 : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := by
    intro u _
    show u • (mat (1 : UA σ G.V'.J) - 1) = 0
    have : mat (1 : UA σ G.V'.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  have hpd : ∀ f f₁ : SInf F (Fin a' × Fin (a + a')),
      ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f f₁ →
      ∀ φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) →
        (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) → IsLineDer om' γ (pure f φ) (pure f₁ φ) := by
    intro f f₁ hf φ hSB hev x
    have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
      (hev.and hP.good.std).mono fun w hw => hw.1.trans hw.2
    exact hf _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd) x
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, hf, φ, hSB, hev, rfl⟩ := hΨ
    obtain ⟨f₁, hf₁⟩ := (hL f hf).1
    refine ⟨pure f₁ φ, hpd f f₁ hf₁ φ hSB hev, fun h hh => ?_⟩
    have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
      (hev.and hP.good.std).mono fun w hw => hw.1.trans hw.2
    obtain ⟨φ₁, ⟨hφ₁, hact⟩, -⟩ := (hA F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP v).1 1 h1 h hh (φ v) (hSB v)
    have hmap : ∀ g : SInf F (Fin a' × Fin (a + a')), om' (1, h) (pure g φ) = pure g (Function.update φ v φ₁) := by
      intro g
      obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v g φ hstd
      have hpure : tens (evFin F v) (φ v) ρ = pure g φ := by rw [hρt, Function.update_eq_self]
      have hRest : Rest (evFin F v) (φ v) ρ := ⟨hρ, by rw [hpure]; exact GlobalTheory.TensUniq.pure_mem_schA g φ hSB hstd⟩
      rw [← hpure, hact ρ hRest, hρt]
    have hSB' : ∀ w, Function.update φ v φ₁ w ∈ SB _ := by
      intro w
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ₁
      · rw [Function.update_of_ne hw]; exact hSB w
    have hev' : ∀ᶠ w in Filter.cofinite, Function.update φ v φ₁ w = G.M'.vac w := by
      filter_upwards [hev, Filter.eventually_cofinite_ne v] with w hw hne
      rw [Function.update_of_ne hne]; exact hw
    rw [hmap f, hmap f₁]
    exact hpd f f₁ hf₁ _ hSB' hev'
  | zero =>
    refine ⟨0, isLineDer_zero om' γ, fun h _ => ?_⟩
    rw [map_zero]; exact isLineDer_zero om' γ
  | add x y _ _ hx hy =>
    obtain ⟨x₁, hdx, hhx⟩ := hx
    obtain ⟨y₁, hdy, hhy⟩ := hy
    refine ⟨x₁ + y₁, isLineDer_add om' γ hdx hdy, fun h hh => ?_⟩
    rw [map_add, map_add]; exact isLineDer_add om' γ (hhx h hh) (hhy h hh)
  | smul c x _ hx =>
    obtain ⟨x₁, hdx, hhx⟩ := hx
    refine ⟨c • x₁, isLineDer_smul om' γ c hdx, fun h hh => ?_⟩
    rw [map_smul, map_smul]; exact isLineDer_smul om' γ c (hhx h hh)

end GlobalTheory.ThKLocSSW

end

noncomputable section

open scoped Classical

namespace GlobalTheory.ThKLocSSW

open GlobalTheory.ThKLocSS GlobalTheory.ThetaFac

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hm N hN v γ hγ Φ hΦ Φ₁ _ hder`. Establish `keyP` using `exists_lineDer_polData' hK hm.triple v hγ`. Establish `key : ∀ Ψ ∈ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∃ Ψ₁ ∈ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), IsLineDer om' γ Ψ Ψ₁ ∧ ∀ h ∈ UAt σ G.W (evFin F v), IsLineDer om' γ (om' (1, h) Ψ) (om' (1, h) Ψ₁)`. Introduce `Ψ hΨ`. Take `⟨Ψ₁, hΨ₁D, hd⟩` from `GlobalTheory.T.matched_triple_finite_maps_forall_places hK F E σ B a a' G X om om' R Rf hm γ hγ Ψ hΨ`.

Take `⟨Ψ₂, hd₂, hh⟩` from `keyP Ψ hΨ.1`. Rewrite `hΨ₁D` using `[isLineDer_unique om' γ hd hd₂]`. Conclude with `⟨Ψ₂, hΨ₁D, hd₂, hh⟩`. Establish `hNder : ∀ Ψ ∈ N, ∀ y, IsLineDer om' γ Ψ y → y ∈ N`. Introduce `Ψ hΨ y hy`.

Take `⟨y', hy'D, hy', -⟩` from `key Ψ (hN.le hΨ)`. Rewrite using `[isLineDer_unique om' γ hy hy']`. Conclude with `hN.stab.lie γ hγ Ψ hΨ y' hy'D hy'`. Establish `hDer : ∀ Ψ ∈ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ y, IsLineDer om' γ Ψ y → y ∈ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) ∧ ∀ h ∈ UAt σ G.W (evFin F v), IsLineDer om' γ (om' (1, h) Ψ) (om' (1, h) y)`. Introduce `Ψ hΨ y hy`.

Take `⟨y', hy'D, hy', hh⟩` from `key Ψ hΨ`. Rewrite using `[isLineDer_unique om' γ hy hy']`. Conclude with `⟨hy'D, hh⟩`. Establish `hsimple : ∀ S, S ≤ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) → IsSimpleOver (opsAt om' v) N S → ∀ Ψ ∈ S, ∀ y, IsLineDer om' γ Ψ y → y ∈ socleOver (opsAt om' v) N ((PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁))`. Introduce `S hSD hS Ψ hΨ y hy`.

Establish `hSst` using `(opStable_opsAt_iff om' v S).1 hS.2.1`. Set `Img : Submodule ℂ (Fn F a' (a + a'))` to `{ carrier := {z | ∃ Ψ ∈ S, IsLineDer om' γ Ψ z} add_mem' := by`. Introduce and unpack `z z' ⟨Ψ, hΨ, hz⟩ ⟨Ψ', hΨ', hz'⟩`. Conclude with `⟨Ψ + Ψ', S.add_mem hΨ hΨ', isLineDer_add om' γ hz hz'⟩`. Use the proof step `zero_mem' := ⟨0, S.zero_mem, isLineDer_zero om' γ⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c z ⟨Ψ, hΨ, hz⟩`. Conclude with `⟨c • Ψ, S.smul_mem c hΨ, isLineDer_smul om' γ c hz⟩ }`. Establish `hyS' : y ∈ N ⊔ Img` using `Submodule.mem_sup_right ⟨Ψ, hΨ, hy⟩`. Establish `hNS : N ≤ S` using `hS.1.le`.

Establish `hS'D : N ⊔ Img ≤ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)` using `sup_le hN.le (fun z ⟨Ψ, hΨ, hz⟩ => (hDer Ψ (hSD hΨ) z hz).1)`. Establish `hImgst : ∀ h ∈ UAt σ G.W (evFin F v), ∀ z ∈ Img, om' (1, h) z ∈ Img`. Introduce and unpack `h hh z ⟨Ψ, hΨ, hz⟩`. Conclude with `⟨om' (1, h) Ψ, hSst h hh Ψ hΨ, (hDer Ψ (hSD hΨ) z hz).2 h hh⟩`. Establish `hS'st : ∀ h ∈ UAt σ G.W (evFin F v), ∀ z ∈ N ⊔ Img, om' (1, h) z ∈ N ⊔ Img`.

Introduce `h hh z hz`. Take `⟨n₀, hn₀, z₀, hz₀, rfl⟩` from `Submodule.mem_sup.1 hz`. Rewrite using `[map_add]`. Conclude with `add_mem (Submodule.mem_sup_left (hN.stab.fin v h hh n₀ hn₀)) (Submodule.mem_sup_right (hImgst h hh z₀ hz₀))`. Distinguish the cases in `hEq : N ⊔ Img = N`.

Conclude with `le_socleOver _ _ _ (hEq ▸ hyS')`. Use `le_socleOver_of_simple _ hS'D ⟨lt_of_le_of_ne le_sup_left (Ne.symm hEq), (opStable_opsAt_iff om' v _).2 hS'st, ?_⟩ hyS'` and prove the remaining obligations. Introduce `S'' hNS'' hS''S' hS''st`. Establish `hS''st'` using `(opStable_opsAt_iff om' v S'').1 hS''st`. Set `Pre : Submodule ℂ (Fn F a' (a + a'))` to `{ carrier := {Ψ | Ψ ∈ S ∧ ∃ z ∈ S'', IsLineDer om' γ Ψ z} add_mem' := by`.

Introduce and unpack `Ψ Ψ' ⟨hΨ, z, hz, hd⟩ ⟨hΨ', z', hz', hd'⟩`. Conclude with `⟨S.add_mem hΨ hΨ', z + z', S''.add_mem hz hz', isLineDer_add om' γ hd hd'⟩`. Use the proof step `zero_mem' := ⟨S.zero_mem, 0, S''.zero_mem, isLineDer_zero om' γ⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c Ψ ⟨hΨ, z, hz, hd⟩`.

Conclude with `⟨S.smul_mem c hΨ, c • z, S''.smul_mem c hz, isLineDer_smul om' γ c hd⟩ }`. Establish `hNPre : N ≤ Pre`. Introduce `Ψ hΨ`. Take `⟨z, -, hz, -⟩` from `key Ψ (hN.le hΨ)`. Conclude with `⟨hNS hΨ, z, hNS'' (hNder Ψ hΨ z hz), hz⟩`.

Establish `hPreS : Pre ≤ S` using `fun Ψ h => h.1`. Establish `hPrest : OpStable (opsAt om' v) Pre`. Rewrite using `[opStable_opsAt_iff]`. Introduce and unpack `h hh Ψ ⟨hΨ, z, hz, hd⟩`. Conclude with `⟨hSst h hh Ψ hΨ, om' (1, h) z, hS''st' h hh z hz, (hDer Ψ (hSD hΨ) z hd).2 h hh⟩`.

Break down `hS.2.2 Pre hNPre hPreS hPrest with hPN | hPS` into its components or cases. Use `left`. Use `le_antisymm ?_ hNS''` and prove the remaining obligations. Introduce `y' hy'`. Take `⟨n₀, hn₀, z₀, ⟨Ψ₀, hΨ₀, hz₀⟩, rfl⟩` from `Submodule.mem_sup.1 (hS''S' hy')`.

Establish `hz₀S'' : z₀ ∈ S''`. Use `S''.sub_mem hy' (hNS'' hn₀)` as an intermediate fact. Simplify using `using this`. Establish `hΨ₀P : Ψ₀ ∈ Pre` using `⟨hΨ₀, z₀, hz₀S'', hz₀⟩`. Rewrite `hΨ₀P` using `[hPN]`.

Conclude with `N.add_mem hn₀ (hNder Ψ₀ hΨ₀P z₀ hz₀)`. Use `right`. Use `le_antisymm hS''S' (sup_le hNS'' ?_)` and prove the remaining obligations. Introduce and unpack `z ⟨Ψ₀, hΨ₀, hz⟩`. Establish `hΨ₀P : Ψ₀ ∈ Pre` using `by rw [hPS]; exact hΨ₀`.

Take `⟨-, z', hz', hd'⟩` from `hΨ₀P`. Rewrite using `[isLineDer_unique om' γ hz hd']`. Conclude with `hz'`. Set `Q : Submodule ℂ (Fn F a' (a + a'))` to `{ carrier := {Ψ | Ψ ∈ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) ∧ ∀ y, IsLineDer om' γ Ψ y → y ∈ socleOver (opsAt om' v) N ((PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁))} zero_mem' := ⟨zero_mem _, fun y hy => by rw [isLineDer_unique om' γ hy (isLineDer_zero om' γ)]; exact zero_mem _⟩ add_mem' : …`. Introduce and unpack `Ψ Ψ' ⟨hΨ, h1⟩ ⟨hΨ', h2⟩`.

Use `⟨add_mem hΨ hΨ', fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨z, -, hz, -⟩` from `key Ψ hΨ`. Take `⟨z', -, hz', -⟩` from `key Ψ' hΨ'`. Rewrite using `[isLineDer_unique om' γ hy (isLineDer_add om' γ hz hz')]`. Conclude with `add_mem (h1 z hz) (h2 z' hz')`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c Ψ ⟨hΨ, h1⟩`. Use `⟨Submodule.smul_mem _ c hΨ, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨z, -, hz, -⟩` from `key Ψ hΨ`. Rewrite using `[isLineDer_unique om' γ hy (isLineDer_smul om' γ c hz)]`.

Conclude with `Submodule.smul_mem _ c (h1 z hz) }`. Establish `hle : socleOver (opsAt om' v) N ((PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) ≤ Q`. Use `sup_le (fun Ψ hΨ => ⟨hN.le hΨ, fun y hy => le_socleOver _ _ _ (hNder Ψ hΨ y hy)⟩) (sSup_le ?_)` and prove the remaining obligations. Introduce and unpack `S ⟨hSD, hS⟩ Ψ hΨ`. Conclude with `⟨hSD hΨ, fun y hy => hsimple S hSD hS Ψ hΨ y hy⟩`.

Conclude with `(hle hΦ).2 Φ₁ hder`.
-/
theorem socleOver_lineDer' : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) N → ∀ v : Pl F, ∀ γ ∈ Lines σ G.W, ∀ Φ ∈ GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om' v) N (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ Φ₁ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om' v) N (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hm N hN v γ hγ Φ hΦ Φ₁ _ hder
  have keyP := exists_lineDer_polData' hK hm.triple v hγ
  have key : ∀ Ψ ∈ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∃ Ψ₁ ∈ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), IsLineDer om' γ Ψ Ψ₁ ∧
      ∀ h ∈ UAt σ G.W (evFin F v), IsLineDer om' γ (om' (1, h) Ψ) (om' (1, h) Ψ₁) := by
    intro Ψ hΨ
    obtain ⟨Ψ₁, hΨ₁D, hd⟩ := GlobalTheory.T.matched_triple_finite_maps_forall_places hK F E σ B a a' G X om om' R Rf hm γ hγ Ψ hΨ
    obtain ⟨Ψ₂, hd₂, hh⟩ := keyP Ψ hΨ.1
    rw [isLineDer_unique om' γ hd hd₂] at hΨ₁D
    exact ⟨Ψ₂, hΨ₁D, hd₂, hh⟩
  have hNder : ∀ Ψ ∈ N, ∀ y, IsLineDer om' γ Ψ y → y ∈ N := by
    intro Ψ hΨ y hy
    obtain ⟨y', hy'D, hy', -⟩ := key Ψ (hN.le hΨ)
    rw [isLineDer_unique om' γ hy hy']
    exact hN.stab.lie γ hγ Ψ hΨ y' hy'D hy'
  have hDer : ∀ Ψ ∈ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ y, IsLineDer om' γ Ψ y →
      y ∈ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) ∧ ∀ h ∈ UAt σ G.W (evFin F v), IsLineDer om' γ (om' (1, h) Ψ) (om' (1, h) y) := by
    intro Ψ hΨ y hy
    obtain ⟨y', hy'D, hy', hh⟩ := key Ψ hΨ
    rw [isLineDer_unique om' γ hy hy']
    exact ⟨hy'D, hh⟩
  have hsimple : ∀ S, S ≤ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) → IsSimpleOver (opsAt om' v) N S → ∀ Ψ ∈ S, ∀ y, IsLineDer om' γ Ψ y →
      y ∈ socleOver (opsAt om' v) N ((PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) := by
    intro S hSD hS Ψ hΨ y hy
    have hSst := (opStable_opsAt_iff om' v S).1 hS.2.1
    let Img : Submodule ℂ (Fn F a' (a + a')) :=
      { carrier := {z | ∃ Ψ ∈ S, IsLineDer om' γ Ψ z}
        add_mem' := by
          rintro z z' ⟨Ψ, hΨ, hz⟩ ⟨Ψ', hΨ', hz'⟩
          exact ⟨Ψ + Ψ', S.add_mem hΨ hΨ', isLineDer_add om' γ hz hz'⟩
        zero_mem' := ⟨0, S.zero_mem, isLineDer_zero om' γ⟩
        smul_mem' := by
          rintro c z ⟨Ψ, hΨ, hz⟩
          exact ⟨c • Ψ, S.smul_mem c hΨ, isLineDer_smul om' γ c hz⟩ }
    have hyS' : y ∈ N ⊔ Img := Submodule.mem_sup_right ⟨Ψ, hΨ, hy⟩
    have hNS : N ≤ S := hS.1.le
    have hS'D : N ⊔ Img ≤ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) := sup_le hN.le (fun z ⟨Ψ, hΨ, hz⟩ => (hDer Ψ (hSD hΨ) z hz).1)
    have hImgst : ∀ h ∈ UAt σ G.W (evFin F v), ∀ z ∈ Img, om' (1, h) z ∈ Img := by
      rintro h hh z ⟨Ψ, hΨ, hz⟩
      exact ⟨om' (1, h) Ψ, hSst h hh Ψ hΨ, (hDer Ψ (hSD hΨ) z hz).2 h hh⟩
    have hS'st : ∀ h ∈ UAt σ G.W (evFin F v), ∀ z ∈ N ⊔ Img, om' (1, h) z ∈ N ⊔ Img := by
      intro h hh z hz
      obtain ⟨n₀, hn₀, z₀, hz₀, rfl⟩ := Submodule.mem_sup.1 hz
      rw [map_add]
      exact add_mem (Submodule.mem_sup_left (hN.stab.fin v h hh n₀ hn₀)) (Submodule.mem_sup_right (hImgst h hh z₀ hz₀))
    by_cases hEq : N ⊔ Img = N
    · exact le_socleOver _ _ _ (hEq ▸ hyS')
    · refine le_socleOver_of_simple _ hS'D ⟨lt_of_le_of_ne le_sup_left (Ne.symm hEq),
        (opStable_opsAt_iff om' v _).2 hS'st, ?_⟩ hyS'
      intro S'' hNS'' hS''S' hS''st
      have hS''st' := (opStable_opsAt_iff om' v S'').1 hS''st
      let Pre : Submodule ℂ (Fn F a' (a + a')) :=
        { carrier := {Ψ | Ψ ∈ S ∧ ∃ z ∈ S'', IsLineDer om' γ Ψ z}
          add_mem' := by
            rintro Ψ Ψ' ⟨hΨ, z, hz, hd⟩ ⟨hΨ', z', hz', hd'⟩
            exact ⟨S.add_mem hΨ hΨ', z + z', S''.add_mem hz hz', isLineDer_add om' γ hd hd'⟩
          zero_mem' := ⟨S.zero_mem, 0, S''.zero_mem, isLineDer_zero om' γ⟩
          smul_mem' := by
            rintro c Ψ ⟨hΨ, z, hz, hd⟩
            exact ⟨S.smul_mem c hΨ, c • z, S''.smul_mem c hz, isLineDer_smul om' γ c hd⟩ }
      have hNPre : N ≤ Pre := by
        intro Ψ hΨ
        obtain ⟨z, -, hz, -⟩ := key Ψ (hN.le hΨ)
        exact ⟨hNS hΨ, z, hNS'' (hNder Ψ hΨ z hz), hz⟩
      have hPreS : Pre ≤ S := fun Ψ h => h.1
      have hPrest : OpStable (opsAt om' v) Pre := by
        rw [opStable_opsAt_iff]
        rintro h hh Ψ ⟨hΨ, z, hz, hd⟩
        exact ⟨hSst h hh Ψ hΨ, om' (1, h) z, hS''st' h hh z hz, (hDer Ψ (hSD hΨ) z hd).2 h hh⟩
      rcases hS.2.2 Pre hNPre hPreS hPrest with hPN | hPS
      · left
        refine le_antisymm ?_ hNS''
        intro y' hy'
        obtain ⟨n₀, hn₀, z₀, ⟨Ψ₀, hΨ₀, hz₀⟩, rfl⟩ := Submodule.mem_sup.1 (hS''S' hy')
        have hz₀S'' : z₀ ∈ S'' := by
          have := S''.sub_mem hy' (hNS'' hn₀)
          simpa using this
        have hΨ₀P : Ψ₀ ∈ Pre := ⟨hΨ₀, z₀, hz₀S'', hz₀⟩
        rw [hPN] at hΨ₀P
        exact N.add_mem hn₀ (hNder Ψ₀ hΨ₀P z₀ hz₀)
      · right
        refine le_antisymm hS''S' (sup_le hNS'' ?_)
        rintro z ⟨Ψ₀, hΨ₀, hz⟩
        have hΨ₀P : Ψ₀ ∈ Pre := by rw [hPS]; exact hΨ₀
        obtain ⟨-, z', hz', hd'⟩ := hΨ₀P
        rw [isLineDer_unique om' γ hz hd']
        exact hz'
  let Q : Submodule ℂ (Fn F a' (a + a')) :=
    { carrier := {Ψ | Ψ ∈ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) ∧ ∀ y, IsLineDer om' γ Ψ y → y ∈ socleOver (opsAt om' v) N ((PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁))}
      zero_mem' := ⟨zero_mem _, fun y hy => by rw [isLineDer_unique om' γ hy (isLineDer_zero om' γ)]; exact zero_mem _⟩
      add_mem' := by
        rintro Ψ Ψ' ⟨hΨ, h1⟩ ⟨hΨ', h2⟩
        refine ⟨add_mem hΨ hΨ', fun y hy => ?_⟩
        obtain ⟨z, -, hz, -⟩ := key Ψ hΨ
        obtain ⟨z', -, hz', -⟩ := key Ψ' hΨ'
        rw [isLineDer_unique om' γ hy (isLineDer_add om' γ hz hz')]
        exact add_mem (h1 z hz) (h2 z' hz')
      smul_mem' := by
        rintro c Ψ ⟨hΨ, h1⟩
        refine ⟨Submodule.smul_mem _ c hΨ, fun y hy => ?_⟩
        obtain ⟨z, -, hz, -⟩ := key Ψ hΨ
        rw [isLineDer_unique om' γ hy (isLineDer_smul om' γ c hz)]
        exact Submodule.smul_mem _ c (h1 z hz) }
  have hle : socleOver (opsAt om' v) N ((PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) ≤ Q := by
    refine sup_le (fun Ψ hΨ => ⟨hN.le hΨ, fun y hy => le_socleOver _ _ _ (hNder Ψ hΨ y hy)⟩) (sSup_le ?_)
    rintro S ⟨hSD, hS⟩ Ψ hΨ
    exact ⟨hSD hΨ, fun y hy => hsimple S hSD hS Ψ hΨ y hy⟩
  exact (hle hΦ).2 Φ₁ hder

end GlobalTheory.ThKLocSSW

end
