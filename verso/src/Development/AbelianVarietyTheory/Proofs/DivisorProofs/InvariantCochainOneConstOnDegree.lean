import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterFunctionOfFibreDerivZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetMorphismExtendingTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainEqOfSameDegreeChartMorphismStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}

/- English proof (translation)
The claim follows from `hm ▸ e`.
-/
theorem le_of_deg_eq {K : Charts F} {m m' : Λ} {a b : K.K} (e : K.le m a b) (hm : m = m') : K.le m' a b :=
  hm ▸ e

/- English proof (translation)
Substitute `hm` using the available equality. Both sides reduce to the same expression.
-/
theorem ptHom_deg_eq (K : Charts F) {m m' : Λ} {k : K.K} (T : K.Obj) (e : K.le m T.k k) (hm : m = m') :
    ptHom T e = ptHom T (le_of_deg_eq e hm) := by
  subst hm; rfl

/- English proof (translation)
The claim follows from `hom_ext (fun c ↦ show T.ρ (sh e₂ (sh e c)) = T.ρ (sh (K.le_trans e e₂) c) by rw [sh_sh]) rfl`.
-/
theorem ptHom_triv_comp (K : Charts F) {l m : Λ} {k k' : K.K} (e : K.le l k' k) (T : K.Obj)
    (e₂ : K.le m T.k k') : ptHom (K.triv k') e ≫ ptHom T e₂ = ptHom T (K.le_trans e e₂) :=
  hom_ext (fun c ↦ show T.ρ (sh e₂ (sh e c)) = T.ρ (sh (K.le_trans e e₂) c) by rw [sh_sh]) rfl

/- English proof (translation)
The claim follows from `hom_ext (fun c ↦ show T.ρ (sh e c) = T.ρ (sh (K.le_refl T.k) (sh e c)) by rw [sh_refl]) (add_zero m).symm`.
-/
theorem ptHom_eq_comp (K : Charts F) {m : Λ} {k : K.K} (T : K.Obj) (e : K.le m T.k k) :
    ptHom T e = ptHom (K.triv T.k) e ≫ ptHom T (K.le_refl T.k) :=
  hom_ext (fun c ↦ show T.ρ (sh e c) = T.ρ (sh (K.le_refl T.k) (sh e c)) by rw [sh_refl]) (add_zero m).symm

/- English proof (translation)
Introduce `I _ g Λ _ F K hK h l hA hB`. Set `B : ∀ k' k : K.K, K.le l k' k → Hol (K.W k')` to `fun k' k e ↦ h _ _ (ptHom (K.triv k') e)`. Establish `hBv : ∀ {m : Λ} {k k' : K.K} (e : K.le m k' k) (hm : m = l), h _ _ (ptHom (K.triv k') e) = B k' k (le_of_deg_eq e hm)`. Introduce `m k k' e hm`. Rewrite using `[ptHom_deg_eq K (K.triv k') e hm]`.

Establish `hR : ∀ {k k' k'' : K.K} (e : K.le l k' k) (e₂ : K.le 0 k'' k'), sh e₂ (B k' k e) = B k'' k (le_of_deg_eq (K.le_trans e e₂) (add_zero l))`. Introduce `k k' k'' e e₂`. Use `hA _ _ _ (ptHom (K.triv k') e) (ptHom (K.triv k'') e₂) rfl rfl` as an intermediate fact. Rewrite `this` using `[ptHom_triv_comp, hBv _ (add_zero l)]`. Conclude with `this.symm`.

Establish `hC : ∀ {k₀ k k' : K.K} (e₀ : K.le 0 k k₀) (e : K.le l k' k), B k' k₀ (le_of_deg_eq (K.le_trans e₀ e) (zero_add l)) = B k' k e`. Introduce `k₀ k k' e₀ e`. Use `hB _ _ _ (ptHom (K.triv k) e₀) (ptHom (K.triv k') e) rfl rfl` as an intermediate fact. Rewrite `this` using `[ptHom_triv_comp, hBv _ (zero_add l)]`. Conclude with `this`.

Establish `hD : ∀ {k k' : K.K} (e : K.le l k' k) (a : Fin g), dw a (B k' k e) = 0`. Introduce `k k' e a`. Take `⟨χ, hχ, h0, h1, -⟩` from `GlobalTheory.T.exists_jet_morphism_extending_translation K e`. Establish `e0` using `hB _ _ _ (jet0 k) χ rfl hχ`. Establish `e1` using `hB _ _ _ (jet1 k) χ rfl hχ`.

Rewrite `e0` using `[h0, hA _ _ _ (ptHom (K.triv k') e) (jet0 k') rfl rfl]`. Rewrite `e1` using `[h1, hA _ _ _ (ptHom (K.triv k') e) (jet1 k') rfl rfl]`. Use `congrArg (fun x : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k')) ↦ x.snd a) (e0.trans e1.symm)` as an intermediate fact. Establish `s0 : ∀ x : Hol (K.W k'), ((jet0 k').φ x : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k'))).snd a = 0` using `fun x ↦ by show (TrivSqZeroExt.inl (sh (K.le_refl k') x) : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k'))).snd a = 0`. Rewrite using `[TrivSqZeroExt.snd_inl]`.

Both sides reduce to the same expression. Establish `s1 : ∀ x : Hol (K.W k'), ((jet1 k').φ x : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k'))).snd a = dw a x` using `fun x ↦ snd_tszeSec _ x a`. Simplify using `only at this`. Rewrite `this` using `[s0, s1]`. Conclude with `this.symm`.

Set `K' : Charts F` to `{ K := {x : K.K × K.K // K.le l x.1 x.2} W := fun x ↦ K.W x.1.1 base := fun x ↦ K.base x.1.1 le := fun m x y ↦ K.le m x.1.1 y.1.1 ∧ K.le m x.1.2 y.1.2 le_refl := fun x ↦ ⟨K.le_refl _, K.le_refl _⟩ le_trans := fun h h' ↦ ⟨K.le_trans h.1 h'.1, K.le_trans h.2 h'.2⟩ maps := fun h ↦ K …`. Establish `hK' : K'.Rich`. Use `⟨fun q hq ↦ ?_, fun m x y q hq hq' ↦ ?_⟩` and prove the remaining obligations. Take `⟨k₀, h₀⟩` from `hK.1 q hq`. Take `⟨k₂, h₂⟩` from `hK.1 (F.shift l q) hq`.

Take `⟨k₃, h₃, -, e₃⟩` from `hK.2 l k₀ k₂ q h₀ h₂`. Conclude with `⟨⟨(k₃, k₂), e₃⟩, h₃⟩`. Take `⟨⟨k₁', k₁⟩, e₁⟩` from `x`. Take `⟨⟨k₂', k₂⟩, e₂⟩` from `y`. Express the relevant statement in the definitionally equal form `q ∈ K.W k₁' at hq`.

Express the relevant statement in the definitionally equal form `F.shift m q ∈ K.W k₂' at hq'`. Establish `p1 : F.shift l q ∈ K.W k₁` using `K.maps e₁ q hq`. Establish `p2 : F.shift m (F.shift l q) ∈ K.W k₂`. Rewrite using `[← F.shift_add, add_comm, F.shift_add]`. Conclude with `K.maps e₂ _ hq'`.

Take `⟨k, hk, f₀, fm⟩` from `hK.2 m k₁ k₂ _ p1 p2`. Take `⟨k₅, h₅, g₀, gm⟩` from `hK.2 m k₁' k₂' q hq hq'`. Take `⟨k', hk', j₀, jl⟩` from `hK.2 l k₅ k q h₅ hk`. Conclude with `⟨⟨(k', k), jl⟩, hk', ⟨le_of_deg_eq (K.le_trans g₀ j₀) (add_zero 0), f₀⟩, ⟨le_of_deg_eq (K.le_trans gm j₀) (add_zero m), fm⟩⟩`. Take `⟨p, hp⟩` from `GlobalTheory.AnPer.Charts.exists_cst_of_dw_eq_zero K' hK' (fun x ↦ B x.1.1 x.1.2 x.2) (fun x y e ↦ by show sh (K := K) e.1 (B _ _ x.2) = B _ _ y.2`.

Rewrite using `[hR x.2 e.1]`. Conclude with `hC e.2 y.2)`. Use the proof step `(fun x i ↦ hD x.2 i)`. Establish `hp' : ∀ (k' k : K.K) (e : K.le l k' k), B k' k e = K.cst k' p` using `fun k' k e ↦ hp ⟨(k', k), e⟩`. Establish `hPt : ∀ {m : Λ} {k : K.K} (T' : K.Obj) (e : K.le m T'.k k), m = l → h _ _ (ptHom T' e) = algebraMap (Hol F.V) T'.C p`.

Introduce `m k T' e hm`. Establish `s4` using `hA _ _ _ (ptHom (K.triv T'.k) e) (ptHom T' (K.le_refl T'.k)) hm rfl`. Rewrite `s4` using `[← ptHom_eq_comp, hBv e hm, hp']`. Rewrite using `[s4]`. Use `show T'.ρ (sh (K.le_refl T'.k) (K.cst T'.k p)) = _`.

Rewrite using `[sh_cst, T'.ρ_cst]`. Use `⟨p, fun T T' φ hφ ↦ ?_⟩` and prove the remaining obligations. Establish `hd : (ptHom T (K.le_refl T.k) ≫ φ).deg = l` using `by show 0 + φ.deg = l`. Rewrite using `[zero_add, hφ]`. Establish `s1` using `hB _ _ _ (ptHom T (K.le_refl T.k)) φ rfl hφ`.

Establish `s2` using `GlobalTheory.T.cochain_eq_of_same_degree_chartMorphism K h l (fun k T χ hχ ↦ (hB _ _ _ (jet0 k) χ rfl hχ).trans (hB _ _ _ (jet1 k) χ rfl hχ).symm) _ T' (ptHom T (K.le_refl T.k) ≫ φ) hd`. Rewrite using `[← s1, s2]`. Conclude with `hPt T' _ hd`.
-/
theorem invCochain_const : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F), K.Rich → ∀ (h : C1 K.Oc) (l : Λ),
    (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = l → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ)) →
    (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = l →
      h T T'' (φ ≫ ψ) = h T' T'' ψ) →
    ∃ p : Hol F.V, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = l → h T T' φ = algebraMap (Hol F.V) T'.C p := by
  intro I _ g Λ _ F K hK h l hA hB

  let B : ∀ k' k : K.K, K.le l k' k → Hol (K.W k') := fun k' k e ↦ h _ _ (ptHom (K.triv k') e)
  have hBv : ∀ {m : Λ} {k k' : K.K} (e : K.le m k' k) (hm : m = l),
      h _ _ (ptHom (K.triv k') e) = B k' k (le_of_deg_eq e hm) := by
    intro m k k' e hm
    rw [ptHom_deg_eq K (K.triv k') e hm]

  have hR : ∀ {k k' k'' : K.K} (e : K.le l k' k) (e₂ : K.le 0 k'' k'),
      sh e₂ (B k' k e) = B k'' k (le_of_deg_eq (K.le_trans e e₂) (add_zero l)) := by
    intro k k' k'' e e₂
    have := hA _ _ _ (ptHom (K.triv k') e) (ptHom (K.triv k'') e₂) rfl rfl
    rw [ptHom_triv_comp, hBv _ (add_zero l)] at this
    exact this.symm

  have hC : ∀ {k₀ k k' : K.K} (e₀ : K.le 0 k k₀) (e : K.le l k' k),
      B k' k₀ (le_of_deg_eq (K.le_trans e₀ e) (zero_add l)) = B k' k e := by
    intro k₀ k k' e₀ e
    have := hB _ _ _ (ptHom (K.triv k) e₀) (ptHom (K.triv k') e) rfl rfl
    rw [ptHom_triv_comp, hBv _ (zero_add l)] at this
    exact this

  have hD : ∀ {k k' : K.K} (e : K.le l k' k) (a : Fin g), dw a (B k' k e) = 0 := by
    intro k k' e a
    obtain ⟨χ, hχ, h0, h1, -⟩ := GlobalTheory.T.exists_jet_morphism_extending_translation K e
    have e0 := hB _ _ _ (jet0 k) χ rfl hχ
    have e1 := hB _ _ _ (jet1 k) χ rfl hχ
    rw [h0, hA _ _ _ (ptHom (K.triv k') e) (jet0 k') rfl rfl] at e0
    rw [h1, hA _ _ _ (ptHom (K.triv k') e) (jet1 k') rfl rfl] at e1
    have := congrArg (fun x : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k')) ↦ x.snd a) (e0.trans e1.symm)
    have s0 : ∀ x : Hol (K.W k'), ((jet0 k').φ x : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k'))).snd a = 0 :=
      fun x ↦ by
        show (TrivSqZeroExt.inl (sh (K.le_refl k') x) : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k'))).snd a = 0
        rw [TrivSqZeroExt.snd_inl]; rfl
    have s1 : ∀ x : Hol (K.W k'), ((jet1 k').φ x : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k'))).snd a = dw a x :=
      fun x ↦ snd_tszeSec _ x a
    simp only at this
    rw [s0, s1] at this
    exact this.symm

  let K' : Charts F :=
    { K := {x : K.K × K.K // K.le l x.1 x.2}
      W := fun x ↦ K.W x.1.1
      base := fun x ↦ K.base x.1.1
      le := fun m x y ↦ K.le m x.1.1 y.1.1 ∧ K.le m x.1.2 y.1.2
      le_refl := fun x ↦ ⟨K.le_refl _, K.le_refl _⟩
      le_trans := fun h h' ↦ ⟨K.le_trans h.1 h'.1, K.le_trans h.2 h'.2⟩
      maps := fun h ↦ K.maps h.1 }
  have hK' : K'.Rich := by
    refine ⟨fun q hq ↦ ?_, fun m x y q hq hq' ↦ ?_⟩
    · obtain ⟨k₀, h₀⟩ := hK.1 q hq
      obtain ⟨k₂, h₂⟩ := hK.1 (F.shift l q) hq
      obtain ⟨k₃, h₃, -, e₃⟩ := hK.2 l k₀ k₂ q h₀ h₂
      exact ⟨⟨(k₃, k₂), e₃⟩, h₃⟩
    · obtain ⟨⟨k₁', k₁⟩, e₁⟩ := x
      obtain ⟨⟨k₂', k₂⟩, e₂⟩ := y
      change q ∈ K.W k₁' at hq
      change F.shift m q ∈ K.W k₂' at hq'
      have p1 : F.shift l q ∈ K.W k₁ := K.maps e₁ q hq
      have p2 : F.shift m (F.shift l q) ∈ K.W k₂ := by
        rw [← F.shift_add, add_comm, F.shift_add]; exact K.maps e₂ _ hq'
      obtain ⟨k, hk, f₀, fm⟩ := hK.2 m k₁ k₂ _ p1 p2
      obtain ⟨k₅, h₅, g₀, gm⟩ := hK.2 m k₁' k₂' q hq hq'
      obtain ⟨k', hk', j₀, jl⟩ := hK.2 l k₅ k q h₅ hk
      exact ⟨⟨(k', k), jl⟩, hk', ⟨le_of_deg_eq (K.le_trans g₀ j₀) (add_zero 0), f₀⟩,
        ⟨le_of_deg_eq (K.le_trans gm j₀) (add_zero m), fm⟩⟩
  obtain ⟨p, hp⟩ := GlobalTheory.AnPer.Charts.exists_cst_of_dw_eq_zero K' hK' (fun x ↦ B x.1.1 x.1.2 x.2)
    (fun x y e ↦ by
      show sh (K := K) e.1 (B _ _ x.2) = B _ _ y.2
      rw [hR x.2 e.1]
      exact hC e.2 y.2)
    (fun x i ↦ hD x.2 i)
  have hp' : ∀ (k' k : K.K) (e : K.le l k' k), B k' k e = K.cst k' p := fun k' k e ↦ hp ⟨(k', k), e⟩

  have hPt : ∀ {m : Λ} {k : K.K} (T' : K.Obj) (e : K.le m T'.k k), m = l →
      h _ _ (ptHom T' e) = algebraMap (Hol F.V) T'.C p := by
    intro m k T' e hm
    have s4 := hA _ _ _ (ptHom (K.triv T'.k) e) (ptHom T' (K.le_refl T'.k)) hm rfl
    rw [← ptHom_eq_comp, hBv e hm, hp'] at s4
    rw [s4]
    show T'.ρ (sh (K.le_refl T'.k) (K.cst T'.k p)) = _
    rw [sh_cst, T'.ρ_cst]
  refine ⟨p, fun T T' φ hφ ↦ ?_⟩
  have hd : (ptHom T (K.le_refl T.k) ≫ φ).deg = l := by
    show 0 + φ.deg = l
    rw [zero_add, hφ]
  have s1 := hB _ _ _ (ptHom T (K.le_refl T.k)) φ rfl hφ
  have s2 := GlobalTheory.T.cochain_eq_of_same_degree_chartMorphism K h l
    (fun k T χ hχ ↦ (hB _ _ _ (jet0 k) χ rfl hχ).trans (hB _ _ _ (jet1 k) χ rfl hχ).symm) _ T'
    (ptHom T (K.le_refl T.k) ≫ φ) hd
  rw [← s1, s2]
  exact hPt T' _ hd

end GlobalTheory.AnPer.Charts
