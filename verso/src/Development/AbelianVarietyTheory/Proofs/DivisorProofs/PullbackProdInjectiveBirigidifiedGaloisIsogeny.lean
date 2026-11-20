import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpSchemeMonHomSquareLiftOneRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGaloisCoverGrpSchemeSquareProductMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorTranslateRatioGlobalUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAxisUnitGeneratorsPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

open GlobalTheory.UPel.HT.Hecke.PullInj in

/- English proof (translation)
Introduce `S A A' _ _ _ _ G ψ hA hA' hψ hG Q₁ Q₂ hQ₁ hQ₂ ⟨ρ₁, hρ₁⟩ ⟨σ₁, hσ₁⟩ ⟨ρ₂, hρ₂⟩ ⟨σ₂, hσ₂⟩ ⟨w, hw⟩`. Establish `hP` using `GlobalTheory.T.isGaloisCover_prod_sq2_of_isGaloisCover S A A' G ψ hψ hG`. Use `hP.finite` as an intermediate fact. Use `hP.fin` as an intermediate fact. Use `hP.etale` as an intermediate fact.

Use `hP.onto` as an intermediate fact. Establish `hT` using `GlobalTheory.LinDescent.locTransitive_of_isGaloisCover hP`. Establish `hA2 : IsAbelianScheme (G2 A)` using `AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA`. Set `π` to `Hecke.sq2 ψ`. Set `τ : ↥G × ↥G → ((G2 A).left ⟶ (G2 A).left)` to `fun h => (Hecke.transl (lift h.1.1 h.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left`.

Establish `hτπ : ∀ c, τ c ≫ π = π` using `hP.inv`. Establish `hτx : ∀ c x, π (τ c x) = π x` using `fun c x => congrArg (fun q : (G2 A).left ⟶ (G2 A').left => q x) (hτπ c)`. Establish `hchart : ∀ x : (G2 A).left, ∃ k, x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k` using `fun x => by`. Take `⟨j₂, h₂⟩` from `exists_chart hQ₂ (π x)`. Take `⟨j₁, h₁⟩` from `exists_chart hQ₁ (π x)`.

Conclude with `⟨(fun _ => j₂, fun _ => j₁), mem_divPull.2 ⟨h₂, h₁⟩⟩`. Set `Inv : ↥G × ↥G → Prop` to `fun c => ∀ (Z : Scheme.{0}) (r : Z ⟶ (G2 A).left) (z : Z) k, r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → gm (r ≫ τ c) z _ (w.s k) = gm r z _ (w.s k)`. Establish `hmul : ∀ a b, Inv a → Inv b → Inv (a * b)` using `fun a b ha hb Z r z k hk => by`. Establish `e : r ≫ τ (a * b) = (r ≫ τ a) ≫ τ b` using `by rw [Category.assoc]; exact congrArg (r ≫ ·) (hP.mul a b)`. Establish `hk' : (r ≫ τ a) z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k`.

Establish `h0` using `(mem_divPull (F := π)).1 hk`. Use `(mem_divPull (F := π)).2 ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `π (τ a (r z)) ∈ _ ∧ π (τ a (r z)) ∈ _`. Rewrite using `[hτx]`. Conclude with `h0`.

Rewrite using `[e, hb Z _ z k hk', ha Z r z k hk]`. Set `s₀ : (G2 A).left ⟶ A.left` to `(toUnit (G2 A) ≫ η[A]).left`. Establish `hs₀ : s₀ ≫ A.hom = (G2 A).hom`. Conclude with `Over.w (toUnit (G2 A) ≫ η[A])`. Establish `axis : ∀ (c : ↥G × ↥G) (e : A.left ⟶ (G2 A).left) (e' : A'.left ⟶ (G2 A').left) (T : A.left ⟶ A.left), e ≫ π = ψ.left ≫ e' → e ≫ (G2 A).hom = A.hom → e ≫ τ c = T ≫ e → T ≫ ψ.left = ψ.left → T ≫ A.hom = A.hom → (∃ ρ : LB.Gen (Q₁.pull e'), ρ.IsGen) → (∃ ρ : LB.Gen (Q₂.pull e'), ρ.I …`.

Introduce and unpack `c e e' T he heS heT hTψ hTS ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩`. Take `⟨f, hf⟩` from `GlobalTheory.T.generator_translate_ratio_global_unit _ _ π Q₁ Q₂ hQ₁ hQ₂ w hw (τ c) (hτπ c)`. Take `⟨g, hg⟩` from `GlobalTheory.T.exists_axis_unit_generators_pullback _ _ _ _ ψ.left e e' π he Q₁ Q₂ hQ₁ hQ₂ w hw r₁ r₂ hr₁ hr₂`. Establish `hTx : ∀ a, ψ.left (T a) = ψ.left a` using `fun a => congrArg (fun q : A.left ⟶ A'.left => q a) hTψ`. Establish `hex : ∀ a, π (e a) = e' (ψ.left a)` using `fun a => congrArg (fun q : A.left ⟶ (G2 A').left => q a) he`.

Establish `hf1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z), gm (r ≫ e) z ⊤ f = 1` using `fun Z r z => by`. Take `⟨k, hk⟩` from `hchart (e (r z))`. Establish `hk' : e ((r ≫ T) z) ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k`. Establish `h0` using `(mem_divPull (F := π)).1 hk`. Use `(mem_divPull (F := π)).2 ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `π (e (T (r z))) ∈ _ ∧ π (e (T (r z))) ∈ _`. Rewrite using `[hex, hTx, ← hex]`. Conclude with `h0`. Establish `h1` using `hf Z (r ≫ e) z k hk`. Establish `h2` using `hg Z r z k hk`.

Establish `h3` using `hg Z (r ≫ T) z k hk'`. Rewrite `h1` using `[Category.assoc, heT, ← Category.assoc]`. Rewrite `h3` using `[Category.assoc r T ψ.left, hTψ, gm_top_eq A hA g (r ≫ T) r (by rw [Category.assoc, hTS])]`. Rewrite `h3` using `[← h2, mul_left_inj]`. Rewrite `h1` using `[h3]`.

Conclude with `(mul_eq_right.1 h1.symm)`. Introduce `Z r z k hk`. Establish `hf' : gm r z ⊤ f = 1`. Rewrite using `[gm_top_eq (G2 A) hA2 f r (r ≫ s₀ ≫ e) (by rw [Category.assoc, Category.assoc, heS, hs₀]), ← Category.assoc]`. Conclude with `hf1 Z (r ≫ s₀) z`.

Rewrite using `[hf Z r z k hk, hf', _root_.one_mul]`. Establish `inv₁ : ∀ h : ↥G, Inv (1, h)` using `fun h => axis (1, h) (lift (1 : A ⟶ A) (𝟙 A)).left (lift (1 : A' ⟶ A') (𝟙 A')).left (Hecke.transl h.1).left (congrArg (·.left) (grpScheme_monHom_square_lift_one_left ψ)) (Over.w _) (by show (lift (1 : A ⟶ A) (𝟙 A)).left ≫ (Hecke.transl (lift ((1 : ↥G) : 𝟙_ (Over S) ⟶ A) h.1)).lef …`. Rewrite using `[OneMemClass.coe_one, ← Over.comp_left, ← Over.comp_left]`. Conclude with `congrArg (·.left) (transl_axis₁ A h.1))`. Use the proof step `(hG.inv h) (Over.w _) ⟨ρ₁, hρ₁⟩ ⟨ρ₂, hρ₂⟩`.

Establish `inv₂ : ∀ h : ↥G, Inv (h, 1)` using `fun h => axis (h, 1) (lift (𝟙 A) (1 : A ⟶ A)).left (lift (𝟙 A') (1 : A' ⟶ A')).left (Hecke.transl h.1).left (congrArg (·.left) (grpScheme_monHom_square_lift_one_right ψ)) (Over.w _) (by show (lift (𝟙 A) (1 : A ⟶ A)).left ≫ (Hecke.transl (lift h.1 ((1 : ↥G) : 𝟙_ (Over S) ⟶ A))).le …`. Rewrite using `[OneMemClass.coe_one, ← Over.comp_left, ← Over.comp_left]`. Conclude with `congrArg (·.left) (transl_axis₂ A h.1))`. Use the proof step `(hG.inv h) (Over.w _) ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩`. Establish `inv : ∀ c, Inv c` using `fun c => by`.

Establish `e : c = (c.1, 1) * (1, c.2)` using `Prod.ext (_root_.mul_one c.1).symm (_root_.one_mul c.2).symm`. Rewrite using `[e]`. Conclude with `hmul _ _ (inv₂ c.1) (inv₁ c.2)`. Establish `hdesc : ∀ p : Q₂.ι × Q₁.ι, ∃ g : Γ((G2 A').left, Q₂.U p.1 ⊓ Q₁.U p.2)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (G2 A).left) (z : Z), r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2) → gm (r ≫ π) z _ g = gm r z _ (w.s (fun _ => p.1, fun _ => p.2))` using `fun p => by`. Take `⟨g, hg⟩` from `GlobalTheory.LinDescent.LocTransitive.exists_descend_unit hT (Q₂.U p.1 ⊓ Q₁.U p.2) (κ := Unit) (fun _ => (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2)) (fun _ x hx => (mem_divPull (F := π)).1 hx) (fun x hx => ⟨(), (mem_divPull (F := π)).2 hx⟩) (fun _ => w.s (fun …`.

Establish `hz' : r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2)` using `(mem_divPull (F := π)).2 hz`. Use `⟨(), (), hz', ?_, inv c Z r z _ hz'⟩` and prove the remaining obligations. Use `(mem_divPull (F := π)).2 ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `π (τ c (r z)) ∈ _ ∧ π (τ c (r z)) ∈ _`. Rewrite using `[hτx]`.

Conclude with `hz)`. Conclude with `⟨g, fun Z r z hz => hg Z r z () hz⟩`. Use `choose g hg using hdesc`. Use `⟨⟨g⟩, fun p q => ?_⟩` and prove the remaining obligations. Apply `GlobalTheory.LinDescent.unit_ext_of_flat (π := π)` to reduce the goal to its premises.

Introduce `x hx`. Establish `hp : x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2)` using `(mem_divPull (F := π)).2 hx.1`. Establish `hq : x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => q.1, fun _ => q.2)` using `(mem_divPull (F := π)).2 hx.2`. Establish `e1` using `gen_germ hw (𝟙 _) x hp hq`. Rewrite `e1` using `[germ_div_g _ _ (𝟙 _) x hp hq, gm_pull_g Q₂ π (𝟙 _) x hx.1.1 hx.2.1, gm_pull_g Q₁ π (𝟙 _) x hx.1.2 hx.2.2]`.

Use `((gm_res (𝟙 _ ≫ π) x inf_le_left hx (g p)).trans (hg p _ (𝟙 _) x hp)).trans ?_` and prove the remaining obligations. Rewrite using `[e1, map_mul, gm_res (𝟙 _ ≫ π) x inf_le_right hx (g q), germ_div_g Q₂ Q₁ (𝟙 _ ≫ π) x hx.1 hx.2]`. Conclude with `congrArg (_ * ·) (hg q _ (𝟙 _) x hq).symm`.
-/
theorem GlobalTheory.UPel.HT.Hecke.pullback_prod_injective_birigidified_galois_isogeny_alt : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (G : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ Q₁ Q₂ : LB (G2 A').left, Q₁.IsLB → Q₂.IsLB → (∃ t : (Q₁.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (Q₁.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → (∃ t : (Q₂.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (Q₂.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Q₁.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) (Q₂.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → LBIso Q₁ Q₂ := by
  intro S A A' _ _ _ _ G ψ hA hA' hψ hG Q₁ Q₂ hQ₁ hQ₂ ⟨ρ₁, hρ₁⟩ ⟨σ₁, hσ₁⟩ ⟨ρ₂, hρ₂⟩ ⟨σ₂, hσ₂⟩ ⟨w, hw⟩
  have hP := GlobalTheory.T.isGaloisCover_prod_sq2_of_isGaloisCover S A A' G ψ hψ hG
  have := hP.finite
  have := hP.fin
  have := hP.etale
  have := hP.onto
  have hT := GlobalTheory.LinDescent.locTransitive_of_isGaloisCover hP
  have hA2 : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  let π := Hecke.sq2 ψ
  let τ : ↥G × ↥G → ((G2 A).left ⟶ (G2 A).left) :=
    fun h => (Hecke.transl (lift h.1.1 h.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left
  have hτπ : ∀ c, τ c ≫ π = π := hP.inv
  have hτx : ∀ c x, π (τ c x) = π x := fun c x => congrArg (fun q : (G2 A).left ⟶ (G2 A').left => q x) (hτπ c)

  have hchart : ∀ x : (G2 A).left, ∃ k, x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := fun x => by
    obtain ⟨j₂, h₂⟩ := exists_chart hQ₂ (π x)
    obtain ⟨j₁, h₁⟩ := exists_chart hQ₁ (π x)
    exact ⟨(fun _ => j₂, fun _ => j₁), mem_divPull.2 ⟨h₂, h₁⟩⟩

  let Inv : ↥G × ↥G → Prop := fun c => ∀ (Z : Scheme.{0}) (r : Z ⟶ (G2 A).left) (z : Z) k,
    r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → gm (r ≫ τ c) z _ (w.s k) = gm r z _ (w.s k)
  have hmul : ∀ a b, Inv a → Inv b → Inv (a * b) := fun a b ha hb Z r z k hk => by
    have e : r ≫ τ (a * b) = (r ≫ τ a) ≫ τ b := by rw [Category.assoc]; exact congrArg (r ≫ ·) (hP.mul a b)
    have hk' : (r ≫ τ a) z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := by
      have h0 := (mem_divPull (F := π)).1 hk
      refine (mem_divPull (F := π)).2 ?_
      change π (τ a (r z)) ∈ _ ∧ π (τ a (r z)) ∈ _
      rw [hτx]; exact h0
    rw [e, hb Z _ z k hk', ha Z r z k hk]

  let s₀ : (G2 A).left ⟶ A.left := (toUnit (G2 A) ≫ η[A]).left
  have hs₀ : s₀ ≫ A.hom = (G2 A).hom := by
    exact Over.w (toUnit (G2 A) ≫ η[A])

  have axis : ∀ (c : ↥G × ↥G) (e : A.left ⟶ (G2 A).left) (e' : A'.left ⟶ (G2 A').left) (T : A.left ⟶ A.left),
      e ≫ π = ψ.left ≫ e' → e ≫ (G2 A).hom = A.hom → e ≫ τ c = T ≫ e → T ≫ ψ.left = ψ.left → T ≫ A.hom = A.hom →
      (∃ ρ : LB.Gen (Q₁.pull e'), ρ.IsGen) → (∃ ρ : LB.Gen (Q₂.pull e'), ρ.IsGen) → Inv c := by
    rintro c e e' T he heS heT hTψ hTS ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩
    obtain ⟨f, hf⟩ := GlobalTheory.T.generator_translate_ratio_global_unit _ _ π Q₁ Q₂ hQ₁ hQ₂ w hw (τ c) (hτπ c)
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_axis_unit_generators_pullback _ _ _ _ ψ.left e e' π he Q₁ Q₂ hQ₁ hQ₂ w hw r₁ r₂ hr₁ hr₂
    have hTx : ∀ a, ψ.left (T a) = ψ.left a := fun a => congrArg (fun q : A.left ⟶ A'.left => q a) hTψ
    have hex : ∀ a, π (e a) = e' (ψ.left a) := fun a => congrArg (fun q : A.left ⟶ (G2 A').left => q a) he
    have hf1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z), gm (r ≫ e) z ⊤ f = 1 := fun Z r z => by
      obtain ⟨k, hk⟩ := hchart (e (r z))
      have hk' : e ((r ≫ T) z) ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := by
        have h0 := (mem_divPull (F := π)).1 hk
        refine (mem_divPull (F := π)).2 ?_
        change π (e (T (r z))) ∈ _ ∧ π (e (T (r z))) ∈ _
        rw [hex, hTx, ← hex]; exact h0
      have h1 := hf Z (r ≫ e) z k hk
      have h2 := hg Z r z k hk
      have h3 := hg Z (r ≫ T) z k hk'
      rw [Category.assoc, heT, ← Category.assoc] at h1
      rw [Category.assoc r T ψ.left, hTψ, gm_top_eq A hA g (r ≫ T) r (by rw [Category.assoc, hTS])] at h3
      rw [← h2, mul_left_inj] at h3
      rw [h3] at h1
      exact (mul_eq_right.1 h1.symm)
    intro Z r z k hk
    have hf' : gm r z ⊤ f = 1 := by
      rw [gm_top_eq (G2 A) hA2 f r (r ≫ s₀ ≫ e) (by rw [Category.assoc, Category.assoc, heS, hs₀]), ← Category.assoc]
      exact hf1 Z (r ≫ s₀) z
    rw [hf Z r z k hk, hf', _root_.one_mul]
  have inv₁ : ∀ h : ↥G, Inv (1, h) := fun h =>
    axis (1, h) (lift (1 : A ⟶ A) (𝟙 A)).left (lift (1 : A' ⟶ A') (𝟙 A')).left (Hecke.transl h.1).left
      (congrArg (·.left) (grpScheme_monHom_square_lift_one_left ψ))
      (Over.w _)
      (by
        show (lift (1 : A ⟶ A) (𝟙 A)).left ≫ (Hecke.transl (lift ((1 : ↥G) : 𝟙_ (Over S) ⟶ A) h.1)).left = _
        rw [OneMemClass.coe_one, ← Over.comp_left, ← Over.comp_left]
        exact congrArg (·.left) (transl_axis₁ A h.1))
      (hG.inv h) (Over.w _) ⟨ρ₁, hρ₁⟩ ⟨ρ₂, hρ₂⟩
  have inv₂ : ∀ h : ↥G, Inv (h, 1) := fun h =>
    axis (h, 1) (lift (𝟙 A) (1 : A ⟶ A)).left (lift (𝟙 A') (1 : A' ⟶ A')).left (Hecke.transl h.1).left
      (congrArg (·.left) (grpScheme_monHom_square_lift_one_right ψ))
      (Over.w _)
      (by
        show (lift (𝟙 A) (1 : A ⟶ A)).left ≫ (Hecke.transl (lift h.1 ((1 : ↥G) : 𝟙_ (Over S) ⟶ A))).left = _
        rw [OneMemClass.coe_one, ← Over.comp_left, ← Over.comp_left]
        exact congrArg (·.left) (transl_axis₂ A h.1))
      (hG.inv h) (Over.w _) ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩
  have inv : ∀ c, Inv c := fun c => by
    have e : c = (c.1, 1) * (1, c.2) := Prod.ext (_root_.mul_one c.1).symm (_root_.one_mul c.2).symm
    rw [e]
    exact hmul _ _ (inv₂ c.1) (inv₁ c.2)

  have hdesc : ∀ p : Q₂.ι × Q₁.ι, ∃ g : Γ((G2 A').left, Q₂.U p.1 ⊓ Q₁.U p.2)ˣ, ∀ (Z : Scheme.{0})
      (r : Z ⟶ (G2 A).left) (z : Z), r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2) →
      gm (r ≫ π) z _ g = gm r z _ (w.s (fun _ => p.1, fun _ => p.2)) := fun p => by
    obtain ⟨g, hg⟩ := GlobalTheory.LinDescent.LocTransitive.exists_descend_unit hT (Q₂.U p.1 ⊓ Q₁.U p.2)
      (κ := Unit) (fun _ => (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2))
      (fun _ x hx => (mem_divPull (F := π)).1 hx)
      (fun x hx => ⟨(), (mem_divPull (F := π)).2 hx⟩)
      (fun _ => w.s (fun _ => p.1, fun _ => p.2)) (fun _ _ _ _ _ => rfl)
      (fun c Z r z hz => by
        have hz' : r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2) :=
          (mem_divPull (F := π)).2 hz
        refine ⟨(), (), hz', ?_, inv c Z r z _ hz'⟩
        refine (mem_divPull (F := π)).2 ?_
        change π (τ c (r z)) ∈ _ ∧ π (τ c (r z)) ∈ _
        rw [hτx]; exact hz)
    exact ⟨g, fun Z r z hz => hg Z r z () hz⟩
  choose g hg using hdesc
  refine ⟨⟨g⟩, fun p q => ?_⟩
  apply GlobalTheory.LinDescent.unit_ext_of_flat (π := π)
  intro x hx
  have hp : x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2) :=
    (mem_divPull (F := π)).2 hx.1
  have hq : x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => q.1, fun _ => q.2) :=
    (mem_divPull (F := π)).2 hx.2
  have e1 := gen_germ hw (𝟙 _) x hp hq
  rw [germ_div_g _ _ (𝟙 _) x hp hq, gm_pull_g Q₂ π (𝟙 _) x hx.1.1 hx.2.1,
    gm_pull_g Q₁ π (𝟙 _) x hx.1.2 hx.2.2] at e1
  refine ((gm_res (𝟙 _ ≫ π) x inf_le_left hx (g p)).trans (hg p _ (𝟙 _) x hp)).trans ?_
  rw [e1, map_mul, gm_res (𝟙 _ ≫ π) x inf_le_right hx (g q), germ_div_g Q₂ Q₁ (𝟙 _ ≫ π) x hx.1 hx.2]
  exact congrArg (_ * ·) (hg q _ (𝟙 _) x hq).symm
