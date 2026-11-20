import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPairDichotomy

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Use `h.map g.appTop.hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.
-/
private theorem isUnit_natCast_of {X Y : Scheme.{0}} (g : X ⟶ Y) {n : ℕ} (h : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    IsUnit ((n : ℕ) : Γ(X, ⊤)) := by
  have := h.map g.appTop.hom
  rwa [map_natCast] at this

/- English proof (translation)
Take `⟨i, hi⟩` from `(hT p D R b N hN hNp _ _ _ _ _ _ o o o₃ (𝟙 S) g).2 g (Category.id_comp g) m m`. Use `⟨i, m.cart.1.hom_ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[hi, Category.id_comp]`. Rewrite using `[i.cart.1.w, Category.comp_id, Category.id_comp]`.
-/
private theorem exists_id {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (hT : ObjTri) (hN : 3 ≤ N) (hNp : N.Coprime p) {S S₃ : Scheme.{0}} {s : S ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o : Obj b N s} {o₃ : Obj b N s₃} {g : S ⟶ S₃} (m : ObjMap o o₃ g) :
    ∃ i : ObjMap o o (𝟙 S), i.φ = 𝟙 _ := by
  obtain ⟨i, hi⟩ := (hT p D R b N hN hNp _ _ _ _ _ _ o o o₃ (𝟙 S) g).2 g (Category.id_comp g) m m
  refine ⟨i, m.cart.1.hom_ext ?_ ?_⟩
  · rw [hi, Category.id_comp]
  · rw [i.cart.1.w, Category.comp_id, Category.id_comp]

/- English proof (translation)
Establish `hpU : IsUnit ((p : ℕ) : Γ((M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme, ⊤))`. Establish `h0` using `GlobalTheory.EtC.PairDich.isUnit_ι_appTop (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) ((p : ℕ) : Γ(M.X, ⊤)) le_rfl`. Rewrite `h0` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hp₀ : IsUnit ((p : ℕ) : Γ(Y₀, ⊤))` using `isUnit_natCast_of gs hpU`. Establish `hpV : IsUnit ((p : ℕ) : Γ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme, ⊤))` using `isUnit_natCast_of (s ∣_ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))) hpU`.

Establish `hPB` using `isPullback_morphismRestrict s (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))`. Take `⟨oV, ⟨mV⟩⟩` from `GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N M.X (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme M.s ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι ≫ s) M.univ`. Take `⟨mVo, -⟩` from `(hT p D R b N hN hNp _ Y M.X _ (s ≫ M.s) M.s oV o M.univ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι s).2 _ rfl mV ms`. Take `⟨oV', mV', ψV, isoV, sqV⟩` from `hI p D R b N Y (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme (s ≫ M.s) _ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι (Category.assoc _ _ _).symm c o o' ψ iso oV mVo`. Establish `tjV` using `(hK p D R b N Y _ (s ≫ M.s) _ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι o o' oV oV' mVo mV' ψ ψV sqV).2 r w j tj`.

Take `⟨y₀, ⟨hy₀, m₀y, m₁y, hsq₀⟩, -⟩` from `hY Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ iso₀ tj₀`. Take `⟨v, ⟨hv, m₀v, m₁v, hsqv⟩, -⟩` from `hY₀ _ ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι ≫ s) oV oV' mV ψV hpV isoV tjV`. Establish `hvy : v ≫ y₀ = (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι`. Apply `(hY _ ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι ≫ s) oV oV' mV ψV hpV isoV tjV).unique` to reduce the goal to its premises. Use `⟨by rw [Category.assoc, hy₀, hv], ?_⟩` and prove the remaining obligations.

Take `⟨a, ha⟩` from `GlobalTheory.HTQuotRigid.objMap_comp_φ m₀v m₀y`. Take `⟨a', ha'⟩` from `GlobalTheory.HTQuotRigid.objMap_comp_φ m₁v m₁y`. Use `⟨a, a', ?_⟩` and prove the remaining obligations. Rewrite using `[ha, ha', Category.assoc m₀v.φ m₀y.φ, hsq₀, ← Category.assoc m₀v.φ, hsqv, Category.assoc (Over.Hom.left ψV) m₁v.φ m₁y.φ]`. Conclude with `⟨rfl, mVo, mV', sqV⟩`.

Set `u : Y₀ ⟶ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme` to `hPB.lift gs y₀ (by rw [hgs, hy₀])`. Establish `hu₁ : u ≫ s ∣_ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) = gs` using `hPB.lift_fst _ _ _`. Establish `hu₂ : u ≫ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι = y₀` using `hPB.lift_snd _ _ _`. Establish `hvg : v ≫ gs = s ∣_ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))`. Rewrite using `[← cancel_mono (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι, Category.assoc, hgs, hv, morphismRestrict_ι]`.

Establish `hvu : v ≫ u = 𝟙 _`. Apply `hPB.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hu₁, hvg, Category.id_comp]`. Rewrite using `[Category.assoc, hu₂, hvy, Category.id_comp]`. Establish `huv : u ≫ v = 𝟙 Y₀`.

Apply `(hY₀ Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ iso₀ tj₀).unique` to reduce the goal to its premises. Use `⟨by rw [Category.assoc, hv, ← Category.assoc, hu₂, hy₀], ?_⟩` and prove the remaining obligations. Establish `hc : (u ≫ v) ≫ y₀ = y₀` using `by rw [Category.assoc, hvy, hu₂]`. Take `⟨a, ha⟩` from `(hT p D R b N hN hNp Y₀ Y₀ Y _ _ _ o₀ o₀ o (u ≫ v) y₀).2 y₀ hc m₀y m₀y`. Take `⟨a', ha'⟩` from `(hT p D R b N hN hNp Y₀ Y₀ Y _ _ _ o₀' o₀' o' (u ≫ v) y₀).2 y₀ hc m₁y m₁y`.

Use `⟨a, a', ?_⟩` and prove the remaining obligations. Apply `m₁y.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc a.φ, ← hsq₀, ← Category.assoc a.φ, ha, hsq₀, Category.assoc (Over.Hom.left ψ₀) a'.φ, ha']`. Establish `e1` using `a.cart.1.w`. Establish `e2` using `a'.cart.1.w`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Category.assoc (Over.Hom.left ψ₀) o₀'.A.hom, ← e2, Category.assoc (Over.Hom.left ψ₀) a'.φ]`. Use `⟨Category.id_comp _, ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_id hT hN hNp ms₀`. Take `⟨i', hi'⟩` from `exists_id hT hN hNp m₁y`.

Conclude with `⟨i, i', by rw [hi, hi', Category.id_comp, Category.comp_id]⟩`. Use `haveI : IsIso v := ⟨⟨u, hvu, huv⟩⟩`. Rewrite using `[← hvg]`. Use `infer_instance`.
-/
private theorem et_of {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (hT : ObjTri) (hI : PullIsog) (hK : PullKer) (hN : 3 ≤ N) (hNp : N.Coprime p)
    {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ}
    {Y : Scheme.{0}} {s : Y ⟶ M.X} {o o' : Obj b N (s ≫ M.s)} (ms : ObjMap o M.univ s) {ψ : o.A ⟶ o'.A}
    (iso : IsPIsog c o o' ψ) (tj : IsTj r w j o o' ψ) (hY : Univ r w j c M s o o' ψ)
    {Y₀ : Scheme.{0}} {s₀ : Y₀ ⟶ M.X} (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme)
    (hgs : gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀) (egs : Etale gs)
    {o₀ o₀' : Obj b N (s₀ ≫ M.s)} (ms₀ : ObjMap o₀ M.univ s₀) {ψ₀ : o₀.A ⟶ o₀'.A}
    (iso₀ : IsPIsog c o₀ o₀' ψ₀) (tj₀ : IsTj r w j o₀ o₀' ψ₀) (hY₀ : Univ r w j c M s₀ o₀ o₀' ψ₀) :
    Etale (s ∣_ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) := by
  have hpU : IsUnit ((p : ℕ) : Γ((M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme, ⊤)) := by
    have h0 := GlobalTheory.EtC.PairDich.isUnit_ι_appTop (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) ((p : ℕ) : Γ(M.X, ⊤)) le_rfl
    rwa [map_natCast] at h0
  have hp₀ : IsUnit ((p : ℕ) : Γ(Y₀, ⊤)) := isUnit_natCast_of gs hpU
  have hpV : IsUnit ((p : ℕ) : Γ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme, ⊤)) :=
    isUnit_natCast_of (s ∣_ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))) hpU
  have hPB := isPullback_morphismRestrict s (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))
  obtain ⟨oV, ⟨mV⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N M.X (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme M.s
    ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι ≫ s) M.univ
  obtain ⟨mVo, -⟩ := (hT p D R b N hN hNp _ Y M.X _ (s ≫ M.s) M.s oV o M.univ
    (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι s).2 _ rfl mV ms
  obtain ⟨oV', mV', ψV, isoV, sqV⟩ := hI p D R b N Y (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme
    (s ≫ M.s) _ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι (Category.assoc _ _ _).symm c o o' ψ iso oV mVo
  have tjV := (hK p D R b N Y _ (s ≫ M.s) _ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι
    o o' oV oV' mVo mV' ψ ψV sqV).2 r w j tj
  obtain ⟨y₀, ⟨hy₀, m₀y, m₁y, hsq₀⟩, -⟩ := hY Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ iso₀ tj₀
  obtain ⟨v, ⟨hv, m₀v, m₁v, hsqv⟩, -⟩ :=
    hY₀ _ ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι ≫ s) oV oV' mV ψV hpV isoV tjV
  have hvy : v ≫ y₀ = (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι := by
    apply (hY _ ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι ≫ s) oV oV' mV ψV hpV isoV tjV).unique
    · refine ⟨by rw [Category.assoc, hy₀, hv], ?_⟩
      obtain ⟨a, ha⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₀v m₀y
      obtain ⟨a', ha'⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁v m₁y
      refine ⟨a, a', ?_⟩
      rw [ha, ha', Category.assoc m₀v.φ m₀y.φ, hsq₀, ← Category.assoc m₀v.φ, hsqv,
        Category.assoc (Over.Hom.left ψV) m₁v.φ m₁y.φ]
    · exact ⟨rfl, mVo, mV', sqV⟩
  let u : Y₀ ⟶ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme := hPB.lift gs y₀ (by rw [hgs, hy₀])
  have hu₁ : u ≫ s ∣_ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) = gs := hPB.lift_fst _ _ _
  have hu₂ : u ≫ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι = y₀ := hPB.lift_snd _ _ _
  have hvg : v ≫ gs = s ∣_ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) := by
    rw [← cancel_mono (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι, Category.assoc, hgs, hv, morphismRestrict_ι]
  have hvu : v ≫ u = 𝟙 _ := by
    apply hPB.hom_ext
    · rw [Category.assoc, hu₁, hvg, Category.id_comp]
    · rw [Category.assoc, hu₂, hvy, Category.id_comp]
  have huv : u ≫ v = 𝟙 Y₀ := by
    apply (hY₀ Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ iso₀ tj₀).unique
    · refine ⟨by rw [Category.assoc, hv, ← Category.assoc, hu₂, hy₀], ?_⟩
      have hc : (u ≫ v) ≫ y₀ = y₀ := by rw [Category.assoc, hvy, hu₂]
      obtain ⟨a, ha⟩ := (hT p D R b N hN hNp Y₀ Y₀ Y _ _ _ o₀ o₀ o (u ≫ v) y₀).2 y₀ hc m₀y m₀y
      obtain ⟨a', ha'⟩ := (hT p D R b N hN hNp Y₀ Y₀ Y _ _ _ o₀' o₀' o' (u ≫ v) y₀).2 y₀ hc m₁y m₁y
      refine ⟨a, a', ?_⟩
      apply m₁y.cart.1.hom_ext
      · rw [Category.assoc a.φ, ← hsq₀, ← Category.assoc a.φ, ha, hsq₀, Category.assoc (Over.Hom.left ψ₀) a'.φ, ha']
      · have e1 := a.cart.1.w
        have e2 := a'.cart.1.w
        calc (a.φ ≫ Over.Hom.left ψ₀) ≫ o₀'.A.hom = a.φ ≫ o₀.A.hom := by rw [Category.assoc a.φ, Over.w]
          _ = o₀.A.hom ≫ (u ≫ v) := e1
          _ = (Over.Hom.left ψ₀ ≫ o₀'.A.hom) ≫ (u ≫ v) := by rw [Over.w]
          _ = (Over.Hom.left ψ₀ ≫ a'.φ) ≫ o₀'.A.hom := by
            rw [Category.assoc (Over.Hom.left ψ₀) o₀'.A.hom, ← e2, Category.assoc (Over.Hom.left ψ₀) a'.φ]
    · refine ⟨Category.id_comp _, ?_⟩
      obtain ⟨i, hi⟩ := exists_id hT hN hNp ms₀
      obtain ⟨i', hi'⟩ := exists_id hT hN hNp m₁y
      exact ⟨i, i', by rw [hi, hi', Category.id_comp, Category.comp_id]⟩
  haveI : IsIso v := ⟨⟨u, hvu, huv⟩⟩
  rw [← hvg]
  infer_instance

/- English proof (translation)
Introduce `hE hG hT hI hK p _ D O _ _ _ _ f b N r w _ hS M j hj`. Establish `hf : 0 < f`. Break down `Nat.eq_zero_or_pos f with rfl | h` into its components or cases. Establish `h1` using `hS.norm`. Rewrite `h1` using `[pow_zero, Ideal.absNorm_eq_one_iff]`.

Conclude with `absurd h1 (Ideal.IsMaximal.ne_top inferInstance)`. Conclude with `h`. Establish `hc : ∃ e : ℕ, p ^ (f * j) = p ^ e ∧ (0 < j → 0 < e)` using `⟨f * j, rfl, fun h => Nat.mul_pos hf h⟩`. Take `⟨Y, s, t, o, o', ms, mt, ψ, st, fin, -, -, flat, iso, tj, univ⟩` from `hE p D O b N hS.three hS.cop hS.pmem r w j (p ^ (f * j)) inferInstance hS.ule hj hc hS.m1 M`. Take `⟨Y₀, s₀, t₀, gs, gt, o₀, o₀', ms₀, mt₀, ψ₀, -, hgs, -, -, egs, -, -, iso₀, tj₀, univ₀⟩` from `hG p D O b N hS.three hS.cop hS.pmem r w j (p ^ (f * j)) inferInstance hS.ule hj hc hS.m1 M`.

Conclude with `⟨⟨Y, s, t, st, o, o', ms, mt, ψ, fin, et_of hT hI hK hS.three hS.cop ms iso tj univ gs hgs egs ms₀ iso₀ tj₀ univ₀, iso, tj, univ⟩, flat⟩`.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.tjExF_of :
    EsNorm → EsGen → ObjTri → PullIsog → PullKer → TjExF := by
  intro hE hG hT hI hK p _ D O _ _ _ _ f b N r w _ hS M j hj
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have h1 := hS.norm
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at h1
      exact absurd h1 (Ideal.IsMaximal.ne_top inferInstance)
    · exact h
  have hc : ∃ e : ℕ, p ^ (f * j) = p ^ e ∧ (0 < j → 0 < e) :=
    ⟨f * j, rfl, fun h => Nat.mul_pos hf h⟩
  obtain ⟨Y, s, t, o, o', ms, mt, ψ, st, fin, -, -, flat, iso, tj, univ⟩ :=
    hE p D O b N hS.three hS.cop hS.pmem r w j (p ^ (f * j)) inferInstance hS.ule hj hc hS.m1 M
  obtain ⟨Y₀, s₀, t₀, gs, gt, o₀, o₀', ms₀, mt₀, ψ₀, -, hgs, -, -, egs, -, -, iso₀, tj₀, univ₀⟩ :=
    hG p D O b N hS.three hS.cop hS.pmem r w j (p ^ (f * j)) inferInstance hS.ule hj hc hS.m1 M
  exact ⟨⟨Y, s, t, st, o, o', ms, mt, ψ, fin,
    et_of hT hI hK hS.three hS.cop ms iso tj univ gs hgs egs ms₀ iso₀ tj₀ univ₀, iso, tj, univ⟩, flat⟩
