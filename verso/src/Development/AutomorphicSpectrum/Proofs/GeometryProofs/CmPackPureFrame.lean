import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmLieModelActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackEigenPeriod
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorsBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelWithCmAction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsAction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PureTypeProjectionIndependent
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveZNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

/- English proof (translation)
Establish `hmem : w ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ ↔ ∀ a : 𝓞 E, ∀ k, ty k (a : E) * w k = τ (a : E) * w k`. Simplify using `only [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[hρ, hχ, funext_iff]`. Both sides reduce to the same expression.

Rewrite using `[hmem]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `k`. Unfold `tyPart`.

Use `split_ifs with hk`. Both sides reduce to the same expression. Establish `: ∃ a : 𝓞 E, ty k (a : E) ≠ τ (a : E)`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hk (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hc))`. Take `⟨a, ha⟩` from `this`. Establish `h2` using `h a k`. Establish `: (ty k (a : E) - τ (a : E)) * w k = 0` using `by rw [sub_mul, h2, sub_self]`. Conclude with `((mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha)).symm`.

Introduce `h a k`. Distinguish the cases in `hk : ty k = τ`. Rewrite using `[hk]`. Establish `: w k = 0`. Use `congrFun h k` as an intermediate fact.

Simplify using `only [tyPart, hk, if_false] at this`. Conclude with `this.symm`. Rewrite using `[this, mul_zero, mul_zero]`.
-/
theorem mem_eigSp_iff_tyPart_eq_self {E : Type} [Field E] [NumberField E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ)
    (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (hρ : ∀ a w, ρ a w = fun k => ty k (a : E) * w k)
    (χ : 𝓞 E →+* ℂ) (hχ : ∀ a, χ a = τ (a : E)) (w : Fin g → ℂ) :
    w ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ ↔ tyPart ty τ w = w := by
  have hmem : w ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ ↔ ∀ a : 𝓞 E, ∀ k, ty k (a : E) * w k = τ (a : E) * w k := by
    simp only [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun a => ?_
    rw [hρ, hχ, funext_iff]
    rfl
  rw [hmem]
  constructor
  · intro h
    funext k
    unfold tyPart
    split_ifs with hk
    · rfl
    · have : ∃ a : 𝓞 E, ty k (a : E) ≠ τ (a : E) := by
        by_contra hc
        push Not at hc
        exact hk (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hc))
      obtain ⟨a, ha⟩ := this
      have h2 := h a k
      have : (ty k (a : E) - τ (a : E)) * w k = 0 := by rw [sub_mul, h2, sub_self]
      exact ((mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha)).symm
  · intro h a k
    by_cases hk : ty k = τ
    · rw [hk]
    · have : w k = 0 := by
        have := congrFun h k
        simp only [tyPart, hk, if_false] at this
        exact this.symm
      rw [this, mul_zero, mul_zero]

end GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl.Frames

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c g ty FU i Z P hP X x hx τ hty hτ hli`. Establish `key : ∀ (b : Bool) (σ : E →+* ℂ) (n : ℕ) (T : Fin n → Fin g → ℂ) (v : Fin n → (epsAt (under X.y) ⟶ Xo.univ.t.G)), LinearIndependent ℂ T → (∀ w, w ∈ Submodule.span ℂ (Set.range T) ↔ tyPart ty σ w = w) → (∀ a, IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • T a) (spMap (dualMap …`. Introduce `b σ n T v hT hspan hd`. Take `⟨⟨v', hv'⟩, hiff⟩` from `GlobalTheory.CompanionTheory.Relay.tangent_vectors_base_change E H _ Xo.univ.t X.K ℂ (algebraMap X.K ℂ) (under X.y) (FU.u i P) (X.β.comp (tauIn c σ)) n v X.pt.symm`. Rewrite using `[hiff v' hv']`.

Take `⟨M, ρ, hact, hρ, hder, -⟩` from `GlobalTheory.CompanionTheory.Relay.lie_model_with_cm_action E H D l Xo c g ty FU i P hP`. Establish `hz` using `GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero E H _ (Z b)`. Take `⟨-, huniq, -⟩` from `GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo (algebraMap (KA l) ℂ) g ty FU i P hP`. Establish `e : ∀ a, v' a = M.pt ((Z b).z • T a)` using `fun a => by`. Take `⟨t, -, htu⟩` from `huniq ((Z b).z • T a)`.

Establish `h1 : IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • T a) (v' a).left`. Rewrite using `[hv' a]`. Conclude with `hd a`. Conclude with `Over.OverMorphism.ext ((htu _ h1).trans (htu _ (hder _)).symm)`. Establish `ev : v' = fun a => M.pt ((Z b).z • T a)` using `funext e`.

Substitute `ev` using the available equality. Rewrite using `[((GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame _ ℂ _ _ _ M).2 (𝓞 E) Xo.univ.t.act ρ _ hact).2 n fun a => (Z b).z • T a]`. Use `⟨hT.units_smul fun _ => Units.mk0 _ hz, ?_⟩` and prove the remaining obligations. Establish `hsp : Submodule.span ℂ (Set.range fun a => (Z b).z • T a) = Submodule.span ℂ (Set.range T)`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `: T a = ((Z b).z)⁻¹ • ((Z b).z • T a)` using `by rw [smul_smul, inv_mul_cancel₀ hz, one_smul]`. Rewrite using `[SetLike.mem_coe, this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`. Rewrite using `[hsp]`. Use extensionality with `w`. Rewrite using `[hspan, GlobalTheory.CompanionTheory.Ar.Fl.mem_eigSp_iff_tyPart_eq_self ty σ ρ hρ _ (fun a => rfl) w]`. Establish `hpq : D.p + D.q = (FU.Di i).p + (FU.Di i).q` using `by rw [(FU.sig i).1, (FU.sig i).2]`.

Take `⟨⟨hl1, hs1⟩, hl2, hs2⟩` from `GlobalTheory.CompanionTheory.Ar.Fl.tyPart_pure_family_bases E H (FU.Di i) g ty P hP D.p D.q x τ hty hpq hτ hx hli`. Use `⟨?_, fun v w hvw => ⟨X.hy, le_refl _, ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨M, ρ, lam, -, -, -, -, -, hcm⟩` from `GlobalTheory.T.cm_lie_model_action E H D l Xo c g ty FU i Z P hP X`. Conclude with `⟨fun a => M.pt (HT.eigProj ρ (X.β.comp (tauE c τ)) (lam true ⟨x (.inl a), hx.1 a⟩)), fun j => M.pt (HT.eigProj ρ (X.β.comp (tauE c (ComplexEmbedding.conjugate τ))) (lam false ⟨x (.inr j), hx.2 j⟩)), fun a => (hcm _ _ _ _).2 rfl, fun j => (hcm _ _ _ _).2 rfl⟩`. Conclude with `key true τ D.p (fun a => tyPart ty τ (P (x (.inl a)))) v hl1 hs1 fun a => GlobalTheory.CompanionTheory.Ar.Fl.CoordPart.isDerivAt0_of_isCMVec E H D l Xo c g ty FU i Z P hP X true τ _ (v a) (hvw.1 a)`.

Conclude with `key false (ComplexEmbedding.conjugate τ) D.q (fun j => tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr j)))) w hl2 hs2 fun j => GlobalTheory.CompanionTheory.Ar.Fl.CoordPart.isDerivAt0_of_isCMVec E H D l Xo c g ty FU i Z P hP X false (ComplexEmbedding.conjugate τ) _ (w j) (hv …`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.cm_pack_pure_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (τ : E →+* ℂ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → LinearIndependent (𝓞 E) x → (∃ v w, X.IsCMFrame τ hx v w) ∧ ∀ v w, X.IsCMFrame τ hx v w → IsFramed (Set.range X.y) τ X.β X.y v w := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X x hx τ hty hτ hli

  have key : ∀ (b : Bool) (σ : E →+* ℂ) (n : ℕ) (T : Fin n → Fin g → ℂ) (v : Fin n → (epsAt (under X.y) ⟶ Xo.univ.t.G)),
      LinearIndependent ℂ T → (∀ w, w ∈ Submodule.span ℂ (Set.range T) ↔ tyPart ty σ w = w) →
      (∀ a, IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • T a)
        (spMap (dualMap (algebraMap X.K ℂ)) ≫ (v a).left)) →
      IsEigFrame Xo.univ.t.act (under X.y) (X.β.comp (tauIn c σ)) v := by
    intro b σ n T v hT hspan hd
    obtain ⟨⟨v', hv'⟩, hiff⟩ := GlobalTheory.CompanionTheory.Relay.tangent_vectors_base_change E H _ Xo.univ.t X.K ℂ (algebraMap X.K ℂ) (under X.y) (FU.u i P)
      (X.β.comp (tauIn c σ)) n v X.pt.symm
    rw [hiff v' hv']
    obtain ⟨M, ρ, hact, hρ, hder, -⟩ := GlobalTheory.CompanionTheory.Relay.lie_model_with_cm_action E H D l Xo c g ty FU i P hP
    have hz := GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero E H _ (Z b)
    obtain ⟨-, huniq, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo (algebraMap (KA l) ℂ) g ty FU i P hP
    have e : ∀ a, v' a = M.pt ((Z b).z • T a) := fun a => by
      obtain ⟨t, -, htu⟩ := huniq ((Z b).z • T a)
      have h1 : IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • T a) (v' a).left := by
        rw [hv' a]; exact hd a
      exact Over.OverMorphism.ext ((htu _ h1).trans (htu _ (hder _)).symm)
    have ev : v' = fun a => M.pt ((Z b).z • T a) := funext e
    subst ev
    rw [((GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame _ ℂ _ _ _ M).2 (𝓞 E) Xo.univ.t.act ρ _ hact).2 n fun a => (Z b).z • T a]
    refine ⟨hT.units_smul fun _ => Units.mk0 _ hz, ?_⟩
    have hsp : Submodule.span ℂ (Set.range fun a => (Z b).z • T a) = Submodule.span ℂ (Set.range T) := by
      apply le_antisymm
      · exact Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨a, rfl⟩
        have : T a = ((Z b).z)⁻¹ • ((Z b).z • T a) := by rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
        rw [SetLike.mem_coe, this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [hsp]
    ext w
    rw [hspan, GlobalTheory.CompanionTheory.Ar.Fl.mem_eigSp_iff_tyPart_eq_self ty σ ρ hρ _ (fun a => rfl) w]
  have hpq : D.p + D.q = (FU.Di i).p + (FU.Di i).q := by rw [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨⟨hl1, hs1⟩, hl2, hs2⟩ := GlobalTheory.CompanionTheory.Ar.Fl.tyPart_pure_family_bases E H (FU.Di i) g ty P hP D.p D.q x τ hty hpq hτ hx hli
  refine ⟨?_, fun v w hvw => ⟨X.hy, le_refl _, ?_, ?_⟩⟩
  · obtain ⟨M, ρ, lam, -, -, -, -, -, hcm⟩ := GlobalTheory.T.cm_lie_model_action E H D l Xo c g ty FU i Z P hP X
    exact ⟨fun a => M.pt (HT.eigProj ρ (X.β.comp (tauE c τ)) (lam true ⟨x (.inl a), hx.1 a⟩)),
      fun j => M.pt (HT.eigProj ρ (X.β.comp (tauE c (ComplexEmbedding.conjugate τ))) (lam false ⟨x (.inr j), hx.2 j⟩)),
      fun a => (hcm _ _ _ _).2 rfl, fun j => (hcm _ _ _ _).2 rfl⟩
  · exact key true τ D.p (fun a => tyPart ty τ (P (x (.inl a)))) v hl1 hs1
      fun a => GlobalTheory.CompanionTheory.Ar.Fl.CoordPart.isDerivAt0_of_isCMVec E H D l Xo c g ty FU i Z P hP X true τ _ (v a) (hvw.1 a)
  · exact key false (ComplexEmbedding.conjugate τ) D.q (fun j => tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr j)))) w hl2 hs2
      fun j => GlobalTheory.CompanionTheory.Ar.Fl.CoordPart.isDerivAt0_of_isCMVec E H D l Xo c g ty FU i Z P hP X false (ComplexEmbedding.conjugate τ) _ (w j) (hvw.2 j)

end GlobalTheory.CompanionTheory.Ar.Fl.Frames
