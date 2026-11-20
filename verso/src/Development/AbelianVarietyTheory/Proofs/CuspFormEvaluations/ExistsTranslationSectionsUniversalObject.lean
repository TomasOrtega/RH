import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsUniqueIsTwistPull
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIsoStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftExistsUniqueGlobalStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TranslExist

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

/- English proof (translation)
Unfold `LB.wchart`. Use `show y ∈ (⋂ k, (φ k) ⁻¹' (L.U (j k) : Set X)) ↔ _`. Simplify using `only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`.
-/
private theorem mem_wchart_lemma {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : K → L.ι) (y : Y) : y ∈ L.wchart φ j ↔ ∀ k, φ k y ∈ L.U (j k) := by
  unfold LB.wchart
  show y ∈ (⋂ k, (φ k) ⁻¹' (L.U (j k) : Set X)) ↔ _
  simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]

/- English proof (translation)
Unfold `IsTwistPull at h' h''`. Establish `hf : ∀ i, s'.f i = s''.f i`. Introduce `i`. Take `⟨i0, rfl⟩ : ∃ i0 : L.ι, i = (fun _ : Fin 1 => i0)` from `⟨i 0, funext fun k => by fin_cases k; rfl⟩`. Apply `fn_ext` to reduce the goal to its premises.

Introduce `x hx`. Establish `hx0 : (snd T A).left x ∈ L.U i0` using `(mem_wchart_lemma L (fun _ : Fin 1 => (snd T A).left) (fun _ => i0) x).mp hx 0`. Choose the witnesses or unpack the hypotheses as in `⟨j1, hj1, hj1'⟩ : ∃ j1 : L.ι, m.left x ∈ L.U j1 ∧ (m.left = (snd T A).left → j1 = i0) := by`. Distinguish the cases in `e : m.left = (snd T A).left`. Conclude with `⟨i0, by rw [e]; exact hx0, fun _ => rfl⟩`.

Establish `hc : m.left x ∈ (⨆ k, L.U k)` using `by rw [hL.cover]; trivial`. Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.mp hc`. Conclude with `⟨k, hk, fun h => absurd h e⟩`. Set `j : Fin 2 → L.ι` to `![i0, j1]`. Establish `hxW : x ∈ L.wchart ![(snd T A).left, m.left] j`.

Rewrite using `[mem_wchart_lemma]`. Introduce `k`. Use `fin_cases k`. Conclude with `hx0`. Conclude with `hj1`.

Take `⟨J, hJ, hJk⟩` from `exists_good L hL x ![(snd T A).left, m.left] j (by`. Introduce `p q hpq`. Apply the tactic sequence `fin_cases p <;> fin_cases q`. Both sides reduce to the same expression. Conclude with `(hj1' hpq.symm).symm`.

Conclude with `hj1' hpq`. Use the proof step `rfl) (by`. Introduce `k`. Use `fin_cases k`. Conclude with `hx0`.

Conclude with `hj1)`. Establish `hv` using `h x J hJ`. Rewrite `hv` using `[val_of α (𝟙 _) x J j (fun k => by rw [Category.id_comp]; exact hJk k), val_of α' (𝟙 _) x J j (fun k => by rw [Category.id_comp]; exact hJk k)]`. Establish `hle : L.wchart ![(snd T A).left, m.left] j ≤ (LPow A L a T).U (fun _ : Fin 1 => i0)`. Introduce `y hy`.

Conclude with `(mem_wchart_lemma L (fun _ : Fin 1 => (snd T A).left) (fun _ => i0) y).mpr (fun _ => (mem_wchart_lemma L _ j y).mp hy 0)`. Establish `e1` using `congrArg (gs (𝟙 _) x (L.wchart ![(snd T A).left, m.left] j)) (h' j)`. Establish `e2` using `congrArg (gs (𝟙 _) x (L.wchart ![(snd T A).left, m.left] j)) (h'' j)`. Rewrite `e1`, `e2` using `[gs_mul _ _ _ hxW]`. Establish `hu : gs (𝟙 (T ⊗ A).left) x (L.wchart ![(snd T A).left, m.left] j) (α.s j).val = gs (𝟙 (T ⊗ A).left) x (L.wchart ![(snd T A).left, m.left] j) (α'.s j).val`.

Conclude with `(gs_unit (𝟙 (T ⊗ A).left) x _ hxW (α.s j)).trans ((congrArg Units.val hv).trans (gs_unit (𝟙 (T ⊗ A).left) x _ hxW (α'.s j)).symm)`. Establish `r1` using `gs_res (𝟙 (T ⊗ A).left) x hle hxW (s'.f fun _ => i0)`. Establish `r2` using `gs_res (𝟙 (T ⊗ A).left) x hle hxW (s''.f fun _ => i0)`. Conclude with `r1.symm.trans (e1.trans ((congrArg (· * _) hu).trans (e2.symm.trans r2)))`. Take `⟨f1, p1⟩` from `s'`.

Take `⟨f2, p2⟩` from `s''`. Establish `: f1 = f2` using `funext hf`. Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
theorem twist_congr (hL : L.IsLB) {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
    {α α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    (h : ∀ y J, Good L y J → val α (𝟙 _) y J = val α' (𝟙 _) y J) {s : LB.Sec (LPow A L b T)}
    {s' s'' : LB.Sec (LPow A L a T)} (h' : IsTwistPull A L ψ m hm a b α s s')
    (h'' : IsTwistPull A L ψ m hm a b α' s s'') : s' = s'' := by
  unfold IsTwistPull at h' h''
  have hf : ∀ i, s'.f i = s''.f i := by
    intro i
    obtain ⟨i0, rfl⟩ : ∃ i0 : L.ι, i = (fun _ : Fin 1 => i0) := ⟨i 0, funext fun k => by fin_cases k; rfl⟩
    apply fn_ext
    intro x hx
    have hx0 : (snd T A).left x ∈ L.U i0 :=
      (mem_wchart_lemma L (fun _ : Fin 1 => (snd T A).left) (fun _ => i0) x).mp hx 0
    obtain ⟨j1, hj1, hj1'⟩ : ∃ j1 : L.ι, m.left x ∈ L.U j1 ∧ (m.left = (snd T A).left → j1 = i0) := by
      by_cases e : m.left = (snd T A).left
      · exact ⟨i0, by rw [e]; exact hx0, fun _ => rfl⟩
      · have hc : m.left x ∈ (⨆ k, L.U k) := by rw [hL.cover]; trivial
        obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
        exact ⟨k, hk, fun h => absurd h e⟩
    let j : Fin 2 → L.ι := ![i0, j1]
    have hxW : x ∈ L.wchart ![(snd T A).left, m.left] j := by
      rw [mem_wchart_lemma]
      intro k
      fin_cases k
      · exact hx0
      · exact hj1
    obtain ⟨J, hJ, hJk⟩ := exists_good L hL x ![(snd T A).left, m.left] j (by
      intro p q hpq
      fin_cases p <;> fin_cases q
      · rfl
      · exact (hj1' hpq.symm).symm
      · exact hj1' hpq
      · rfl) (by
      intro k
      fin_cases k
      · exact hx0
      · exact hj1)
    have hv := h x J hJ
    rw [val_of α (𝟙 _) x J j (fun k => by rw [Category.id_comp]; exact hJk k),
      val_of α' (𝟙 _) x J j (fun k => by rw [Category.id_comp]; exact hJk k)] at hv
    have hle : L.wchart ![(snd T A).left, m.left] j ≤ (LPow A L a T).U (fun _ : Fin 1 => i0) := by
      intro y hy
      exact (mem_wchart_lemma L (fun _ : Fin 1 => (snd T A).left) (fun _ => i0) y).mpr
        (fun _ => (mem_wchart_lemma L _ j y).mp hy 0)
    have e1 := congrArg (gs (𝟙 _) x (L.wchart ![(snd T A).left, m.left] j)) (h' j)
    have e2 := congrArg (gs (𝟙 _) x (L.wchart ![(snd T A).left, m.left] j)) (h'' j)
    rw [gs_mul _ _ _ hxW] at e1 e2
    have hu : gs (𝟙 (T ⊗ A).left) x (L.wchart ![(snd T A).left, m.left] j) (α.s j).val =
        gs (𝟙 (T ⊗ A).left) x (L.wchart ![(snd T A).left, m.left] j) (α'.s j).val := by
      exact (gs_unit (𝟙 (T ⊗ A).left) x _ hxW (α.s j)).trans
        ((congrArg Units.val hv).trans (gs_unit (𝟙 (T ⊗ A).left) x _ hxW (α'.s j)).symm)
    have r1 := gs_res (𝟙 (T ⊗ A).left) x hle hxW (s'.f fun _ => i0)
    have r2 := gs_res (𝟙 (T ⊗ A).left) x hle hxW (s''.f fun _ => i0)
    exact r1.symm.trans (e1.trans ((congrArg (· * _) hu).trans (e2.symm.trans r2)))
  obtain ⟨f1, p1⟩ := s'
  obtain ⟨f2, p2⟩ := s''
  have : f1 = f2 := funext hf
  subst this
  rfl

/- English proof (translation)
Take `⟨pt, φ, hφ⟩` from `U`. Take `⟨pt', φ', hφ'⟩` from `U'`. Simplify using `only at hp`. Substitute `hp` using the available equality. Unfold `IsActOf at h' h''`.

Conclude with `twist_congr hL (fun y J hJ => val_corr hJ h (𝟙 _)) h' h''`.
-/
theorem act_congr (hL : L.IsLB) {T : Over S} {k : ℤ} {U U' : ThetaGrp A L k T} (hp : U.pt = U'.pt)
    (h : LB.Gen.Corr L _ _ _ _ U.φ U'.φ) {s s' s'' : LB.Sec (LPow A L k T)} (h' : IsActOf A L k U s s')
    (h'' : IsActOf A L k U' s s'') : s' = s'' := by
  obtain ⟨pt, φ, hφ⟩ := U
  obtain ⟨pt', φ', hφ'⟩ := U'
  simp only at hp
  subst hp
  unfold IsActOf at h' h''
  exact twist_congr hL (fun y J hJ => val_corr hJ h (𝟙 _)) h' h''

end TranslExist

open TranslExist in

/- English proof (translation)
Introduce `hLaws E _ _ _ H Dw l Xo N hN T s`. Establish `hL : Xo.univ.t.PP.L.IsLB` using `Xo.univ.t.PP.isLB`. Take `⟨α₀, hg₀, hn₀, hu₀, hT⟩` from `GlobalTheory.T.universal_normalised_mulByNat_pullback_iso hLaws E H Dw l Xo N`. Take `⟨α, hgα, hcα⟩` from `hT T`. Take `⟨s₁, hs₁⟩ : ∃ s₁, IsTwistPull Xo.univ.t.G Xo.univ.t.PP.L (mulT Xo.univ.t.G T N) (snd T Xo.univ.t.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁` from `(existsUnique_isTwistPull _ _ _ hL _ _ _ _ _ _ α hgα s).exists`.

Establish `hact : ∀ (U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T) (a : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T)), ∃ b, IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) U a b`. Introduce `U a`. Unfold `IsActOf`. Conclude with `(existsUnique_isTwistPull _ _ _ hL _ _ _ _ _ _ U.φ U.isGen a).exists`. Use `⟨fun ok t t' h1 h2 h3 => ?_, fun x₁ x₂ hx₁ hx₂ => ?_⟩` and prove the remaining obligations.

Take `⟨U, hU⟩` from `(GlobalTheory.T.universal_symLift_exists_unique_global hLaws E H Dw l Xo N hN T t' h2).1`. Take `⟨F, hF⟩` from `hact U s₁`. Conclude with `⟨F, t', α₀, α, s₁, U, h1, h3, hg₀, hn₀, hcα, hs₁, hU, hF⟩`. Establish `S₁` using `GlobalTheory.T.universal_symLift_exists_unique_global hLaws E H Dw l Xo N hN T x₁ hx₁`. Establish `S₂` using `GlobalTheory.T.universal_symLift_exists_unique_global hLaws E H Dw l Xo N hN T x₂ hx₂`.

Take `⟨U₁, hU₁⟩` from `S₁.1`. Take `⟨U₂, hU₂⟩` from `S₂.1`. Take `⟨s₂, hs₂⟩` from `hact U₁ s₁`. Take `⟨F, hF⟩` from `hact U₂ s₂`. Use `⟨F, ⟨α₀, α, s₁, s₂, U₁, U₂, hg₀, hn₀, hcα, hs₁, hU₁, hs₂, hU₂, hF⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `F' ⟨β₀, β, t₁, t₂, V₁, V₂, hgβ₀, hnβ₀, hcβ, ht₁, hV₁, ht₂, hV₂, hF'⟩`. Establish `e₁ : t₁ = s₁`. Use `twist_congr hL (fun y J hJ => ?_) ht₁ hs₁` and prove the remaining obligations. Conclude with `(val_corr hJ hcβ _).trans ((val_pull hJ β₀ _ _).trans ((val_corr hJ (hu₀ β₀ hgβ₀ hnβ₀) _).trans ((val_corr hJ hcα _).trans (val_pull hJ α₀ _ _)).symm))`. Rewrite `ht₂` using `[e₁]`.

Establish `e₂ : t₂ = s₂` using `act_congr hL (hV₁.pt_eq.trans hU₁.pt_eq.symm) (S₁.2 V₁ U₁ hV₁ hU₁) ht₂ hs₂`. Rewrite `hF'` using `[e₂]`. Conclude with `act_congr hL (hV₂.pt_eq.trans hU₂.pt_eq.symm) (S₂.2 V₂ U₂ hV₂ hU₂) hF' hF`.
-/
theorem exists_isVtOver_and_existsUnique_isUUOver : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T)), (∀ (ok : (T ⟶ Xo.univ.t.G) → Prop) (t t' : T ⟶ Xo.univ.t.G), t' ^ N = t → t' ^ (N ^ 2) = 1 → ok t' → ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP N ok s t F) ∧ ∀ x₁ x₂ : T ⟶ Xo.univ.t.G, x₁ ^ (N ^ 2) = 1 → x₂ ^ (N ^ 2) = 1 → ∃! F, IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F := by
  intro hLaws E _ _ _ H Dw l Xo N hN T s
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  obtain ⟨α₀, hg₀, hn₀, hu₀, hT⟩ := GlobalTheory.T.universal_normalised_mulByNat_pullback_iso hLaws E H Dw l Xo N
  obtain ⟨α, hgα, hcα⟩ := hT T
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, IsTwistPull Xo.univ.t.G Xo.univ.t.PP.L (mulT Xo.univ.t.G T N)
      (snd T Xo.univ.t.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ :=
    (existsUnique_isTwistPull _ _ _ hL _ _ _ _ _ _ α hgα s).exists
  have hact : ∀ (U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T)
      (a : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T)),
      ∃ b, IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) U a b := by
    intro U a
    unfold IsActOf
    exact (existsUnique_isTwistPull _ _ _ hL _ _ _ _ _ _ U.φ U.isGen a).exists
  refine ⟨fun ok t t' h1 h2 h3 => ?_, fun x₁ x₂ hx₁ hx₂ => ?_⟩
  · obtain ⟨U, hU⟩ := (GlobalTheory.T.universal_symLift_exists_unique_global hLaws E H Dw l Xo N hN T t' h2).1
    obtain ⟨F, hF⟩ := hact U s₁
    exact ⟨F, t', α₀, α, s₁, U, h1, h3, hg₀, hn₀, hcα, hs₁, hU, hF⟩
  · have S₁ := GlobalTheory.T.universal_symLift_exists_unique_global hLaws E H Dw l Xo N hN T x₁ hx₁
    have S₂ := GlobalTheory.T.universal_symLift_exists_unique_global hLaws E H Dw l Xo N hN T x₂ hx₂
    obtain ⟨U₁, hU₁⟩ := S₁.1
    obtain ⟨U₂, hU₂⟩ := S₂.1
    obtain ⟨s₂, hs₂⟩ := hact U₁ s₁
    obtain ⟨F, hF⟩ := hact U₂ s₂
    refine ⟨F, ⟨α₀, α, s₁, s₂, U₁, U₂, hg₀, hn₀, hcα, hs₁, hU₁, hs₂, hU₂, hF⟩, ?_⟩
    rintro F' ⟨β₀, β, t₁, t₂, V₁, V₂, hgβ₀, hnβ₀, hcβ, ht₁, hV₁, ht₂, hV₂, hF'⟩
    have e₁ : t₁ = s₁ := by
      refine twist_congr hL (fun y J hJ => ?_) ht₁ hs₁
      exact (val_corr hJ hcβ _).trans ((val_pull hJ β₀ _ _).trans ((val_corr hJ (hu₀ β₀ hgβ₀ hnβ₀) _).trans
        ((val_corr hJ hcα _).trans (val_pull hJ α₀ _ _)).symm))
    rw [e₁] at ht₂
    have e₂ : t₂ = s₂ :=
      act_congr hL (hV₁.pt_eq.trans hU₁.pt_eq.symm) (S₁.2 V₁ U₁ hV₁ hU₁) ht₂ hs₂
    rw [e₂] at hF'
    exact act_congr hL (hV₂.pt_eq.trans hU₂.pt_eq.symm) (S₂.2 V₂ U₂ hV₂ hU₂) hF' hF

end GlobalTheory
