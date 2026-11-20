import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ActsRhoFin
import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsPureML

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF
open scoped Classical

def IdealM : Prop :=
  ∃ a₁ a₂ b₁ b₂ : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (r s r' s' i j i' j' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ i j → H'.IsAdapted σ B W W₁ i' j' → i < n → j < n → i' < d → j' < d →
    ∀ u (e₁ e₂ : ℤˣ), (u = shiftA H H' ∧ e₁ = a₁ ∧ e₂ = a₂) ∨ (u = shiftB σ H H' ∧ e₁ = b₁ ∧ e₂ = b₂) →
    ∃ 𝔞 : FractionalIdeal (𝓞 E)⁰ E, 𝔞 ≠ 0 ∧ (∀ v l, idem F v • u l ∈ latAtV X W v ↔ InAt 𝔞 v (l : AE F E)) ∧
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → FractionalIdeal.count E w 𝔞 = 0) ∧
      ∀ ν : Chr F E, Continuous ν → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range ν 0 → UnrOff ν (B.P : Set (Pl F)) →
        idealVal ν 𝔞 = idealVal ν H.𝔟 ^ (e₁ : ℤ) * idealVal ν H'.𝔟 ^ (e₂ : ℤ)

def FinM : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) e u ei ev, Cfg B M M₁ H H' e u → IsEvLoc M M₁ e ei ev →
    ∀ v : Pl F,
    ∀ (K : Subgroup (UA σ X.J)) (m : LocMeas K), IsStab B K → m.Is → ∀ χX χW om r s r' s', IsPair B M χX χW om r s r' s' →
    ∀ (ν : Chr F E) (z : ℕ), Continuous ν → 2 ≤ z →
    ∃ Λ : Fl F v _ _ →ₗ[ℂ] Fl F v _ _, ∀ φ ∈ SB _, Λ φ = coneF B M om m v (ev v) u ν z φ ∧ Λ φ ∈ SB _ ∧ ∀ y,
      (∀ k : kAt K (evFin F v), @Integrable _ _ _ _ (borel _) (fun l : idAt E (evFin F v) =>
          ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • u l.1) (om (k.1, 1) Φ)) φ) y * wt ν z l.1) (m.xf v)) ∧
        Integrable (fun k : kAt K (evFin F v) => @integral _ _ _ _ (borel _) (m.xf v) fun l =>
          ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • u l.1) (om (k.1, 1) Φ)) φ) y * wt ν z l.1) (m.kf v)

/- English proof (translation)
Establish `e : (fun v => if v ∈ T then A v else w v) = ext w T fun v => A v` using `funext fun v => by`. Apply the tactic sequence `unfold ext; split_ifs <;> rfl`. Rewrite using `[e, pure_ext hw, Finset.prod_coe_sort T fun v => A v fun i => evFin F v (x i)]`.
-/
theorem pure_ite {κ : Type} [Fintype κ] {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hw : Std w) (T : Finset (Pl F)) (f : SInf F κ)
    (A : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x : κ → AF F) :
    pure f (fun v => if v ∈ T then A v else w v) x = f (fun i => evI F (x i)) * ((∏ v ∈ T, A v fun i => evFin F v (x i)) *
      ∏ᶠ (v) (_ : v ∉ T), w v fun i => evFin F v (x i)) := by
  have e : (fun v => if v ∈ T then A v else w v) = ext w T fun v => A v := funext fun v => by
    unfold ext; split_ifs <;> rfl
  rw [e, pure_ext hw, Finset.prod_coe_sort T fun v => A v fun i => evFin F v (x i)]

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

def Concl (B : Base F E) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (om : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)) (ev : ∀ v : Pl F, Fl F v n d →ₗ[ℂ] Fl F v n₁ d₁)
    (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ) (m : LocMeas K) (U : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E))
    (ν : Chr F E) (z : ℕ) (S : Finset (Pl F)) (c₀ : ℂ) : Prop :=
  ∃ (L : SInf F _ →L[ℂ] SInf F _) (Λ : ∀ v : Pl F, Fl F v _ _ →ₗ[ℂ] Fl F v _ _) (u : Pl F → ℂ),
    IsConeI B M om m ei U ν z L ∧ (∀ f ∈ M.Pol B.ψ B.emb, L f ∈ M₁.Pol B.ψ B.emb) ∧
    (∀ v, ∀ φ ∈ SB _, Λ v φ = coneF B M om m v (ev v) U ν z φ ∧ Λ v φ ∈ SB _) ∧
    (∀ v ∉ S, u v ≠ 0 ∧ Λ v (M.vac v) = u v • M₁.vac v) ∧
    (∀ Φ ∈ schA F _, ∀ Ψ ∈ schA F _, ∀ c : ℂ, cone B M om e K μK μ U ν z (Φ + c • Ψ) =
      cone B M om e K μK μ U ν z Φ + c • cone B M om e K μK μ U ν z Ψ) ∧
    ∀ T : Finset (Pl F), S ⊆ T → ∀ (f : SInf F _) φ, (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = M.vac v) →
      (∏ v ∈ T \ S, u v) • cone B M om e K μK μ U ν z (pure f φ) = c₀ • pure (L f) fun v => if v ∈ T then Λ v (φ v) else M₁.vac v

/- English proof (translation)
Take `⟨r₀, s₀, hX⟩` from `hC.herm`. Take `⟨πi, π, κ₁, k1, hπ, HI⟩` from `hI F E σ B n X K m μ hC.base hm h2 𝔞 z h0 hz`. Take `⟨ρi, ρ, κ₂, k2, hρ, HK⟩` from `hKF F E σ B n X r₀ s₀ hC.base hX K m μK hK hm h1`. Use `⟨κ₁ * κ₂, mul_ne_zero k1 k2, fun χX χW om r s r' s' hp ν S₀ S hν hS₀ uν uX uW hram => ?_⟩` and prove the remaining obligations. Take `⟨hu, HT⟩` from `HI ν S₀ S hν hS₀ uν hram`.

Take `⟨L, hL, hLP, hLi⟩` from `hAr F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e U ei ev hC hE K m hK hm χX χW om r s r' s' hp ν z hν (by omega)`. Use `choose Λ hΛ using fun v => hF F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e U ei ev hC hE v K m hK hm χX χW om r s r' s' hp ν z hν hz`. Establish `mono : ∀ {χ : Chr F E} {T : Finset (Pl F)}, S ⊆ T → UnrOff χ (S : Set (Pl F)) → UnrOff χ (T : Set (Pl F))` using `fun hT h w hw => h w fun h' => hw (hT h')`. Set `I : Fn F n d → (Fin n₁ × Fin d₁ → AF F) → K → (AE F E)ˣ → ℂ` to `fun Φ y k l => e (M.co.rho B.ψ (U l) (om (k.1, 1) Φ)) y * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z`. Establish `main : ∀ T : Finset (Pl F), S ⊆ T → ∀ (f : SInf F _) φ, (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = M.vac v) → ∀ y, (∀ k, Integrable (I (pure f φ) y k) μ) ∧ Integrable (fun k => ∫ l, I (pure f φ) y k l ∂μ) μK ∧ (∏ v ∈ T \ S, uLoc v (m.xf v) 𝔞 ν z) * ∫ k, ∫ l, I (pure f φ) y k l ∂μ ∂μK = …`.

Introduce `T hT f φ hSB hvac y`. Set `t : ℂ` to `∏ᶠ (v) (_ : v ∉ T), M₁.vac v fun i => evFin F v (y i)`. Set `gi : kAt K (evI F) → idAt E (evI F) → ℂ` to `fun k l => ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • U l.1) (om (k.1, 1) Φ)) f) fun i => evI F (y i)`. Set `g : ∀ v : Pl F, kAt K (evFin F v) → idAt E (evFin F v) → ℂ` to `fun v k l => ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • U l.1) (om (k.1, 1) Φ)) (φ v)) fun i => evFin F v (y i)`. Establish `e1 : ∀ k l, I (pure f φ) y k l = t * (gi (ρi k) (πi l) * (∏ v ∈ T, g v (ρ v k) (π v l)) * (if ∀ v ∉ T, InAt 𝔞 v (l : AE F E) then 1 else 0) * wt ν z l)` using `fun k l => by`.

Use `hP F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e U ei ev hC hE K hK χX χW om r s r' s' hp T (mono hT uX) (mono hT uW) f φ hSB hvac k.1 k.2 l (ρi k).1 (fun v => (ρ v k).1) (πi l).1 (fun v => (π v l).1) (hρ k).1 (hρ k).2 (hπ l).1 (hπ l).2` as an intermediate fact. Simplify using `only [I, this, hlat, Pi.smul_apply, smul_eq_mul, pure_ite hC.good₁.std, wt, t, gi, g]`. Expand and normalize the polynomial expressions, which then agree. Establish `H1` using `fun k : K => HT T hT (gi (ρi k)) (fun v => g v (ρ v k)) ((hLi f _).1 _) fun v _ => ((hΛ v (φ v) (hSB v)).2.2 _).1 _`. Set `hi : kAt K (evI F) → ℂ` to `fun k => @integral _ _ _ _ (borel _) m.xi fun l => gi k l * wt ν z l.1`.

Set `h : ∀ v : Pl F, kAt K (evFin F v) → ℂ` to `fun v k => @integral _ _ _ _ (borel _) (m.xf v) fun l => g v k l * wt ν z l.1`. Take `⟨i2, e2⟩` from `HK T hi h (hLi f _).2 fun v _ => ((hΛ v (φ v) (hSB v)).2.2 _).2`. Establish `hne : (∏ v ∈ T \ S, uLoc v (m.xf v) 𝔞 ν z) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun v hv => (hu v (Finset.mem_sdiff.1 hv).2).1`. Use `set p := ∏ v ∈ T \ S, uLoc v (m.xf v) 𝔞 ν z`. Use `set c := κ₁ * (idealVal ν 𝔞 : ℂ) * charL ν (S₀ : Set (Pl F)) (z : ℂ) with hc`.

Establish `e3 : ∀ k, ∫ l, I (pure f φ) y k l ∂μ = (p⁻¹ * t * c) * (hi (ρi k) * ∏ v ∈ T, h v (ρ v k))` using `fun k => by`. Simplify using `only [e1]`. Rewrite using `[integral_const_mul]`. Use `(H1 k).2` as an intermediate fact. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises.

Rewrite using `[mul_left_comm, this]`. Clear the denominators using the available nonvanishing facts. Both sides reduce to the same expression. Use `⟨fun k => ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `((H1 k).1.const_mul t).congr (.of_forall fun l => (e1 k l).symm)`.

Simplify using `only [e3]`. Conclude with `i2.const_mul _`. Simplify using `only [e3]`. Rewrite using `[integral_const_mul, e2, pure_ite hC.good₁.std, hL]`. Establish `e4 : ∏ v ∈ T, Λ v (φ v) (fun i => evFin F v (y i)) = ∏ v ∈ T, ∫ k, h v k ∂(m.kf v)` using `Finset.prod_congr rfl fun v _ => by`.

Rewrite using `[(hΛ v (φ v) (hSB v)).1]`. Simplify using `only [coneF, h, g, wt, mul_assoc]`. Rewrite using `[e4]`. Establish `e5 : (∫ k, @integral _ _ _ _ (borel _) m.xi (fun l => ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • U l.1) (om (k.1, 1) Φ)) f) (fun i => evI F (y i)) * (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z) ∂m.ki) = ∫ k, hi k ∂m.ki` using `by simp only [hi, gi, wt, mul_assoc]`. Rewrite using `[e5, hc]`.

Use `show _ = _ * (_ * (_ * t))`. Clear the denominators using the available nonvanishing facts. Use `⟨L, Λ, fun v => uLoc v (m.xf v) 𝔞 ν z, hL, hLP, fun v φ hφ => ⟨(hΛ v φ hφ).1, (hΛ v φ hφ).2.1⟩, fun v hv => ⟨(hu v hv).1, ?_⟩, ?_, fun T hT f φ a b => funext fun y => (main T hT f φ a b y).2.2⟩` and prove the remaining obligations. Rewrite using `[(hΛ v _ (hp.good.vac v).1).1]`. Use function extensionality and compare the values at `y`.

Establish `e1 : ∀ (k : kAt K (evFin F v)) (l : idAt E (evFin F v)), ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • U l.1) (om (k.1, 1) Φ)) (M.vac v)) = if InAt 𝔞 v (l.1 : AE F E) then M₁.vac v else 0` using `fun k l => by`. Take `⟨ξ, hξ, -⟩` from `(hA F E σ B n d X W M χX χW om r s r' s' hp v).2.1 _ (at_idem v (U l.1)) _ (hp.good.vac v).1`. Establish `a` using `hV F E σ B n d X W M χX χW om r s r' s' hp K hK v (fun w hw => ⟨uX w fun h => hv (hw ▸ h), uW w fun h => hv (hw ▸ h)⟩) k.1 k.2`. Rewrite using `[opF_eq (hp.good.vac v).1 hξ.1 (acts_comp (om_pres hp _) a hξ.2), ← opF_eq (hp.good.vac v).1 hξ.1 hξ.2, hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e U ei ev hC hE v l.1]`. Simplify using `only [hlat]`.

Simplify using `only [coneF, e1]`. Rewrite using `[integral_const, Measure.real, (hm.kf v).2, ENNReal.toReal_one, one_smul, Pi.smul_apply, smul_eq_mul, uLoc, ← @integral_mul_const _ (borel _)]`. Use `congr 1`. Use function extensionality and compare the values at `l`. Use `split_ifs`.

Rewrite using `[wt]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish `Iadd : ∀ Φ Ψ (c : ℂ) y k l, I (Φ + c • Ψ) y k l = I Φ y k l + c * I Ψ y k l` using `fun Φ Ψ c y k l => by`. Establish `: M.co.rho B.ψ (U l) (om (k.1, 1) (Φ + c • Ψ)) = M.co.rho B.ψ (U l) (om (k.1, 1) Φ) + c • M.co.rho B.ψ (U l) (om (k.1, 1) Ψ)`.

Rewrite using `[map_add, map_smul]`. Use function extensionality and compare the values at `x`. Simplify using `only [Darboux.rho, schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [I]`.

Rewrite using `[this, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Set `Q : Fn F n d → Prop` to `fun Φ => ∀ y, (∀ k, Integrable (I Φ y k) μ) ∧ Integrable (fun k => ∫ l, I Φ y k l ∂μ) μK`. Establish `inner : ∀ Φ Ψ (c : ℂ), Q Φ → Q Ψ → ∀ y k, ∫ l, I (Φ + c • Ψ) y k l ∂μ = ∫ l, I Φ y k l ∂μ + c * ∫ l, I Ψ y k l ∂μ` using `fun Φ Ψ c a b y k => by`. Simplify using `only [Iadd]`.

Rewrite using `[integral_add ((a y).1 k) (((b y).1 k).const_mul c), integral_const_mul]`. Establish `Qadd : ∀ Φ Ψ (c : ℂ), Q Φ → Q Ψ → Q (Φ + c • Ψ)` using `fun Φ Ψ c a b y => ⟨fun k => (((a y).1 k).add (((b y).1 k).const_mul c)).congr (.of_forall fun l => (Iadd Φ Ψ c y k l).symm), by`. Simplify using `only [inner Φ Ψ c a b]`. Conclude with `(a y).2.add ((b y).2.const_mul c)⟩`. Establish `Q0 : Q 0` using `fun y => by`.

Establish `: ∀ k, I 0 y k = fun _ => 0` using `fun k => funext fun l => by`. Establish `h` using `Iadd 0 0 1 y k l`. Rewrite `h` using `[smul_zero, add_zero, one_mul]`. Conclude with `left_eq_add.1 h`. Simplify using `[this]`.

Establish `QA : ∀ Φ ∈ schA F (Fin n × Fin d), Q Φ` using `fun Φ hΦ => by`. Rewrite `hΦ` using `[hSp F _ M.vac (fun v => (hp.good.vac v).1) hp.good.std]`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, φ, T, a, b, rfl⟩` from `h`.

Conclude with `fun y => let h := main (S ∪ T) Finset.subset_union_left f φ a (fun v hv => b v fun h => hv (Finset.mem_union_right _ h)) y ⟨h.1, h.2.1⟩`. Consider the case `zero => exact Q0`. Consider the case `add a b _ _ ha hb => simpa using Qadd a b 1 ha hb`. Consider the case `smul c a _ ha => simpa using Qadd 0 a c Q0 ha`. Introduce `Φ hΦ Ψ hΨ c`.

Use function extensionality and compare the values at `y`. Use `show ∫ k, ∫ l, I (Φ + c • Ψ) y k l ∂μ ∂μK = ∫ k, ∫ l, I Φ y k l ∂μ ∂μK + c * ∫ k, ∫ l, I Ψ y k l ∂μ ∂μK`. Simplify using `only [inner Φ Ψ c (QA Φ hΦ) (QA Ψ hΨ)]`. Rewrite using `[integral_add (QA Φ hΦ y).2 ((QA Ψ hΨ y).2.const_mul c), integral_const_mul]`.
-/
theorem gen (hA : ActsEx) (hI : IdeleFub) (hKF : KFub) (hV : VacFixX) (hS : VacShift) (hAr : ArchCone) (hF : FinM) (hP : PureFac)
    (hSp : SchSpan) {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H H' e U ei ev} (hC : Cfg B M M₁ H H' e U)
    (hE : IsEvLoc M M₁ e ei ev) {K : Subgroup (UA σ X.J)} {μK : Measure K} {μ : Measure (AE F E)ˣ} {m : LocMeas K} (hK : IsStab B K)
    (h1 : μK.IsHaarMeasure) (h2 : μ.IsHaarMeasure) (hm : m.Is) {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h0 : 𝔞 ≠ 0)
    (hlat : ∀ v l, idem F v • U l ∈ latAtV X W v ↔ InAt 𝔞 v (l : AE F E)) {z : ℕ} (hz : 2 ≤ z) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ (ν : Chr F E) (S₀ S : Finset (Pl F)), Continuous ν → S₀ ⊆ S →
      UnrOff ν (S : Set (Pl F)) → UnrOff χX (S : Set (Pl F)) → UnrOff χW (S : Set (Pl F)) →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ S → ¬ UnrAt ν w ∧ FractionalIdeal.count E w 𝔞 = 0) →
      Concl B M M₁ om e ei ev K μK μ m U ν z S (κ * (idealVal ν 𝔞 : ℂ) * charL ν (S₀ : Set (Pl F)) (z : ℂ)) := by
  obtain ⟨r₀, s₀, hX⟩ := hC.herm
  obtain ⟨πi, π, κ₁, k1, hπ, HI⟩ := hI F E σ B n X K m μ hC.base hm h2 𝔞 z h0 hz
  obtain ⟨ρi, ρ, κ₂, k2, hρ, HK⟩ := hKF F E σ B n X r₀ s₀ hC.base hX K m μK hK hm h1
  refine ⟨κ₁ * κ₂, mul_ne_zero k1 k2, fun χX χW om r s r' s' hp ν S₀ S hν hS₀ uν uX uW hram => ?_⟩
  obtain ⟨hu, HT⟩ := HI ν S₀ S hν hS₀ uν hram
  obtain ⟨L, hL, hLP, hLi⟩ := hAr F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e U ei ev hC hE K m hK hm χX χW om r s r' s' hp ν z hν (by omega)
  choose Λ hΛ using fun v => hF F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e U ei ev hC hE v K m hK hm χX χW om r s r' s' hp ν z hν hz
  have mono : ∀ {χ : Chr F E} {T : Finset (Pl F)}, S ⊆ T → UnrOff χ (S : Set (Pl F)) → UnrOff χ (T : Set (Pl F)) :=
    fun hT h w hw => h w fun h' => hw (hT h')
  let I : Fn F n d → (Fin n₁ × Fin d₁ → AF F) → K → (AE F E)ˣ → ℂ := fun Φ y k l =>
    e (M.co.rho B.ψ (U l) (om (k.1, 1) Φ)) y * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z
  have main : ∀ T : Finset (Pl F), S ⊆ T → ∀ (f : SInf F _) φ, (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = M.vac v) → ∀ y,
      (∀ k, Integrable (I (pure f φ) y k) μ) ∧ Integrable (fun k => ∫ l, I (pure f φ) y k l ∂μ) μK ∧
      (∏ v ∈ T \ S, uLoc v (m.xf v) 𝔞 ν z) * ∫ k, ∫ l, I (pure f φ) y k l ∂μ ∂μK =
        (κ₁ * κ₂ * (idealVal ν 𝔞 : ℂ) * charL ν (S₀ : Set (Pl F)) (z : ℂ)) *
          pure (L f) (fun v => if v ∈ T then Λ v (φ v) else M₁.vac v) y := by
    intro T hT f φ hSB hvac y
    let t : ℂ := ∏ᶠ (v) (_ : v ∉ T), M₁.vac v fun i => evFin F v (y i)
    let gi : kAt K (evI F) → idAt E (evI F) → ℂ := fun k l =>
      ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • U l.1) (om (k.1, 1) Φ)) f) fun i => evI F (y i)
    let g : ∀ v : Pl F, kAt K (evFin F v) → idAt E (evFin F v) → ℂ := fun v k l =>
      ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • U l.1) (om (k.1, 1) Φ)) (φ v)) fun i => evFin F v (y i)
    have e1 : ∀ k l, I (pure f φ) y k l = t * (gi (ρi k) (πi l) * (∏ v ∈ T, g v (ρ v k) (π v l)) *
        (if ∀ v ∉ T, InAt 𝔞 v (l : AE F E) then 1 else 0) * wt ν z l) := fun k l => by
      have := hP F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e U ei ev hC hE K hK χX χW om r s r' s' hp T (mono hT uX) (mono hT uW) f φ hSB hvac
        k.1 k.2 l (ρi k).1 (fun v => (ρ v k).1) (πi l).1 (fun v => (π v l).1) (hρ k).1 (hρ k).2 (hπ l).1 (hπ l).2
      simp only [I, this, hlat, Pi.smul_apply, smul_eq_mul, pure_ite hC.good₁.std, wt, t, gi, g]
      ring
    have H1 := fun k : K => HT T hT (gi (ρi k)) (fun v => g v (ρ v k)) ((hLi f _).1 _) fun v _ => ((hΛ v (φ v) (hSB v)).2.2 _).1 _
    let hi : kAt K (evI F) → ℂ := fun k => @integral _ _ _ _ (borel _) m.xi fun l => gi k l * wt ν z l.1
    let h : ∀ v : Pl F, kAt K (evFin F v) → ℂ := fun v k => @integral _ _ _ _ (borel _) (m.xf v) fun l => g v k l * wt ν z l.1
    obtain ⟨i2, e2⟩ := HK T hi h (hLi f _).2 fun v _ => ((hΛ v (φ v) (hSB v)).2.2 _).2
    have hne : (∏ v ∈ T \ S, uLoc v (m.xf v) 𝔞 ν z) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v hv => (hu v (Finset.mem_sdiff.1 hv).2).1
    set p := ∏ v ∈ T \ S, uLoc v (m.xf v) 𝔞 ν z
    set c := κ₁ * (idealVal ν 𝔞 : ℂ) * charL ν (S₀ : Set (Pl F)) (z : ℂ) with hc
    have e3 : ∀ k, ∫ l, I (pure f φ) y k l ∂μ = (p⁻¹ * t * c) * (hi (ρi k) * ∏ v ∈ T, h v (ρ v k)) := fun k => by
      simp only [e1]
      rw [integral_const_mul]
      have := (H1 k).2
      apply mul_left_cancel₀ hne
      rw [mul_left_comm, this]
      field_simp
      rfl
    refine ⟨fun k => ?_, ?_, ?_⟩
    · exact ((H1 k).1.const_mul t).congr (.of_forall fun l => (e1 k l).symm)
    · simp only [e3]; exact i2.const_mul _
    · simp only [e3]
      rw [integral_const_mul, e2, pure_ite hC.good₁.std, hL]
      have e4 : ∏ v ∈ T, Λ v (φ v) (fun i => evFin F v (y i)) = ∏ v ∈ T, ∫ k, h v k ∂(m.kf v) := Finset.prod_congr rfl fun v _ => by
        rw [(hΛ v (φ v) (hSB v)).1]
        simp only [coneF, h, g, wt, mul_assoc]
      rw [e4]
      have e5 : (∫ k, @integral _ _ _ _ (borel _) m.xi (fun l =>
          ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • U l.1) (om (k.1, 1) Φ)) f) (fun i => evI F (y i)) * (ν l.1 : ℂ) *
            ((absE F E l.1 : ℝ) : ℂ) ^ z) ∂m.ki) = ∫ k, hi k ∂m.ki := by simp only [hi, gi, wt, mul_assoc]
      rw [e5, hc]
      show _ = _ * (_ * (_ * t))
      field_simp
  refine ⟨L, Λ, fun v => uLoc v (m.xf v) 𝔞 ν z, hL, hLP, fun v φ hφ => ⟨(hΛ v φ hφ).1, (hΛ v φ hφ).2.1⟩,
    fun v hv => ⟨(hu v hv).1, ?_⟩, ?_, fun T hT f φ a b => funext fun y => (main T hT f φ a b y).2.2⟩
  · rw [(hΛ v _ (hp.good.vac v).1).1]
    funext y
    have e1 : ∀ (k : kAt K (evFin F v)) (l : idAt E (evFin F v)),
        ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • U l.1) (om (k.1, 1) Φ)) (M.vac v)) =
          if InAt 𝔞 v (l.1 : AE F E) then M₁.vac v else 0 := fun k l => by
      obtain ⟨ξ, hξ, -⟩ := (hA F E σ B n d X W M χX χW om r s r' s' hp v).2.1 _ (at_idem v (U l.1)) _ (hp.good.vac v).1
      have a := hV F E σ B n d X W M χX χW om r s r' s' hp K hK v
        (fun w hw => ⟨uX w fun h => hv (hw ▸ h), uW w fun h => hv (hw ▸ h)⟩) k.1 k.2
      rw [opF_eq (hp.good.vac v).1 hξ.1 (acts_comp (om_pres hp _) a hξ.2), ← opF_eq (hp.good.vac v).1 hξ.1 hξ.2,
        hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e U ei ev hC hE v l.1]
      simp only [hlat]
    simp only [coneF, e1]
    rw [integral_const, Measure.real, (hm.kf v).2, ENNReal.toReal_one, one_smul, Pi.smul_apply, smul_eq_mul, uLoc,
      ← @integral_mul_const _ (borel _)]
    congr 1
    funext l
    split_ifs
    · rw [wt]; ring
    · simp
  · have Iadd : ∀ Φ Ψ (c : ℂ) y k l, I (Φ + c • Ψ) y k l = I Φ y k l + c * I Ψ y k l := fun Φ Ψ c y k l => by
      have : M.co.rho B.ψ (U l) (om (k.1, 1) (Φ + c • Ψ)) = M.co.rho B.ψ (U l) (om (k.1, 1) Φ) + c • M.co.rho B.ψ (U l) (om (k.1, 1) Ψ) := by
        rw [map_add, map_smul]
        funext x
        simp only [Darboux.rho, schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      simp only [I]
      rw [this, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    let Q : Fn F n d → Prop := fun Φ => ∀ y, (∀ k, Integrable (I Φ y k) μ) ∧ Integrable (fun k => ∫ l, I Φ y k l ∂μ) μK
    have inner : ∀ Φ Ψ (c : ℂ), Q Φ → Q Ψ → ∀ y k, ∫ l, I (Φ + c • Ψ) y k l ∂μ = ∫ l, I Φ y k l ∂μ + c * ∫ l, I Ψ y k l ∂μ :=
      fun Φ Ψ c a b y k => by
        simp only [Iadd]
        rw [integral_add ((a y).1 k) (((b y).1 k).const_mul c), integral_const_mul]
    have Qadd : ∀ Φ Ψ (c : ℂ), Q Φ → Q Ψ → Q (Φ + c • Ψ) := fun Φ Ψ c a b y =>
      ⟨fun k => (((a y).1 k).add (((b y).1 k).const_mul c)).congr (.of_forall fun l => (Iadd Φ Ψ c y k l).symm), by
        simp only [inner Φ Ψ c a b]; exact (a y).2.add ((b y).2.const_mul c)⟩
    have Q0 : Q 0 := fun y => by
      have : ∀ k, I 0 y k = fun _ => 0 := fun k => funext fun l => by
        have h := Iadd 0 0 1 y k l
        rw [smul_zero, add_zero, one_mul] at h
        exact left_eq_add.1 h
      simp [this]
    have QA : ∀ Φ ∈ schA F (Fin n × Fin d), Q Φ := fun Φ hΦ => by
      rw [hSp F _ M.vac (fun v => (hp.good.vac v).1) hp.good.std] at hΦ
      induction hΦ using Submodule.span_induction with
      | mem Φ h =>
        obtain ⟨f, φ, T, a, b, rfl⟩ := h
        exact fun y => let h := main (S ∪ T) Finset.subset_union_left f φ a (fun v hv => b v fun h => hv (Finset.mem_union_right _ h)) y
          ⟨h.1, h.2.1⟩
      | zero => exact Q0
      | add a b _ _ ha hb => simpa using Qadd a b 1 ha hb
      | smul c a _ ha => simpa using Qadd 0 a c Q0 ha
    intro Φ hΦ Ψ hΨ c
    funext y
    show ∫ k, ∫ l, I (Φ + c • Ψ) y k l ∂μ ∂μK = ∫ k, ∫ l, I Φ y k l ∂μ ∂μK + c * ∫ k, ∫ l, I Ψ y k l ∂μ ∂μK
    simp only [inner Φ Ψ c (QA Φ hΦ) (QA Ψ hΨ)]
    rw [integral_add (QA Φ hΦ y).2 ((QA Ψ hΨ y).2.const_mul c), integral_const_mul]

end PositivityTheory.ThKG.Loc.Cone

end
