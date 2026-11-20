import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.TriFrDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Establish `key : ∀ l, (∀ k, l < k → C k = 0) → v l = C l * T l l`. Introduce `l hl`. Rewrite using `[h, Finset.sum_apply, Finset.sum_eq_single l]`. Both sides reduce to the same expression. Introduce `k _ hk`.

Break down `lt_or_gt_of_ne hk with hk | hk` into its components or cases. Simplify using `[hT k l hk]`. Simplify using `[hl k hk]`. Simplify using the standard rewrite rules. Establish `h0 : ∀ l, m < l → C l = 0`.

Introduce `l`. Proceed by induction on `l using WellFoundedGT.induction with`. Consider the case `ind l ih`. Introduce `hl`. Use `key l fun k hk => ih k hk (hl.trans hk)` as an intermediate fact.

Rewrite `this` using `[hv l hl]`. Conclude with `(mul_eq_zero.1 this.symm).resolve_right (hd l)`. Conclude with `⟨h0, key m h0⟩`.
-/
private theorem tri_alg {K : Type} [Field K] {n : ℕ} (T : Fin n → Fin n → K) (v C : Fin n → K) (m : Fin n)
    (hd : ∀ l, T l l ≠ 0) (hT : ∀ l k, l < k → T l k = 0) (hv : ∀ k, m < k → v k = 0)
    (h : v = ∑ l, C l • T l) : (∀ l, m < l → C l = 0) ∧ v m = C m * T m m := by
  have key : ∀ l, (∀ k, l < k → C k = 0) → v l = C l * T l l := by
    intro l hl
    rw [h, Finset.sum_apply, Finset.sum_eq_single l]
    · rfl
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · simp [hT k l hk]
      · simp [hl k hk]
    · simp
  have h0 : ∀ l, m < l → C l = 0 := by
    intro l
    induction l using WellFoundedGT.induction with
    | ind l ih =>
      intro hl
      have := key l fun k hk => ih k hk (hl.trans hk)
      rw [hv l hl] at this
      exact (mul_eq_zero.1 this.symm).resolve_right (hd l)
  exact ⟨h0, key m h0⟩

/- English proof (translation)
The claim follows from `hT.fromSpecStalk_eq_fromSpecStalk h`.
-/
private theorem gen_fromSpec {W : Scheme.{0}} [IsIntegral W] {T : W.Opens} (hT : IsAffineOpen T)
    (h : genericPoint W ∈ T) : spMap (fnOf T h) ≫ hT.fromSpec = GlobalTheory.CurveRootGeometry.genPt W :=
  hT.fromSpecStalk_eq_fromSpecStalk h

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {A : Type} [CommRing A] {s : X ⟶ Sp A} {ε : 𝓞 E →+* A} {n : ℕ}

/- English proof (translation)
Take `⟨⟨N, e, u, hu, hb⟩, -⟩` from `h`. Rewrite using `[← hu]`. Conclude with `GlobalTheory.LieMet.isTan_map _ rfl (hb.1 _)`.
-/
private theorem locFr_tan {R S : Type} [CommRing R] [CommRing S] {x₀ : Sp R ⟶ X}
    {w : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (h : GlobalTheory.TriFlag.IsLocFr t s ε x₀ w) (α : R →+* S) (m : Fin n) :
    IsTanAtG t (spMap α ≫ x₀) (spMap (dualMap α) ≫ w m) := by
  obtain ⟨⟨N, e, u, hu, hb⟩, -⟩ := h
  rw [← hu]
  exact GlobalTheory.LieMet.isTan_map _ rfl (hb.1 _)

/- English proof (translation)
Establish `hψ : (spMap α ≫ x₀) ≫ s = spMap (Spec.preimage ((spMap α ≫ x₀) ≫ s)).hom` using `(Spec.map_preimage _).symm`. Conclude with `((h.2 S α _ hψ).2 _ (e ▸ locFr_tan h' α' m) ((h'.2 S α' _ (e ▸ hψ)).1 m)).exists`.
-/
private theorem locFr_comb {R R' S : Type} [CommRing R] [CommRing R'] [CommRing S] {x₀ : Sp R ⟶ X} {x₀' : Sp R' ⟶ X}
    {w : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} {w' : Fin n → (Sp (DualNumber R') ⟶ t.G.left)}
    (h : GlobalTheory.TriFlag.IsLocFr t s ε x₀ w) (h' : GlobalTheory.TriFlag.IsLocFr t s ε x₀' w') (α : R →+* S) (α' : R' →+* S)
    (e : spMap α' ≫ x₀' = spMap α ≫ x₀) (m : Fin n) :
    ∃ C : Fin n → S, IsCombAtG t (spMap α ≫ x₀) (fun l => spMap (dualMap α) ≫ w l) C (spMap (dualMap α') ≫ w' m) := by
  have hψ : (spMap α ≫ x₀) ≫ s = spMap (Spec.preimage ((spMap α ≫ x₀) ≫ s)).hom := (Spec.map_preimage _).symm
  exact ((h.2 S α _ hψ).2 _ (e ▸ locFr_tan h' α' m) ((h'.2 S α' _ (e ▸ hψ)).1 m)).exists

/- English proof (translation)
Use `choose T hT1 hT2 hT3 using h`. Take `⟨v, hv1, hv2, hv3⟩` from `h' m`. Use `hi _ _ _ hv3 (GlobalTheory.LineNorm.Chart.comb_comb hu hT3 (GlobalTheory.LatDRFree.comb_map t φ hC))` as an intermediate fact. Take `⟨h1, h2⟩` from `tri_alg T v _ m (fun l => (hT1 l).symm ▸ hd l) hT2 hv2 this`. Use `⟨hφ (mul_right_cancel₀ (hd m) ?_), fun l hl => hφ ((h1 l hl).trans (map_zero φ).symm)⟩` and prove the remaining obligations.

Rewrite using `[hg, ← hv1, h2, hT1]`.
-/
private theorem tri_comb {S K : Type} [CommRing S] [Field K] {y : Sp S ⟶ X} (φ : S →+* K) (hφ : Function.Injective φ)
    {u : Fin n → (Sp (DualNumber K) ⟶ t.G.left)} (hu : ∀ m, IsTanAtG t (spMap φ ≫ y) (u m))
    (hi : IsIndep t (spMap φ ≫ y) u) {w w' : Fin n → (Sp (DualNumber S) ⟶ t.G.left)} {d d' : Fin n → K}
    (hd : ∀ l, d l ≠ 0) (h : GlobalTheory.TriFlag.IsTriOf t (spMap φ ≫ y) u d fun l => spMap (dualMap φ) ≫ w l)
    (h' : GlobalTheory.TriFlag.IsTriOf t (spMap φ ≫ y) u d' fun l => spMap (dualMap φ) ≫ w' l) {m : Fin n} {C : Fin n → S}
    (hC : IsCombAtG t y w C (w' m)) {g : S} (hg : φ g * d m = d' m) : C m = g ∧ ∀ l, m < l → C l = 0 := by
  choose T hT1 hT2 hT3 using h
  obtain ⟨v, hv1, hv2, hv3⟩ := h' m
  have := hi _ _ _ hv3 (GlobalTheory.LineNorm.Chart.comb_comb hu hT3 (GlobalTheory.LatDRFree.comb_map t φ hC))
  obtain ⟨h1, h2⟩ := tri_alg T v _ m (fun l => (hT1 l).symm ▸ hd l) hT2 hv2 this
  refine ⟨hφ (mul_right_cancel₀ (hd m) ?_), fun l hl => hφ ((h1 l hl).trans (map_zero φ).symm)⟩
  rw [hg, ← hv1, h2, hT1]

end

/- English proof (translation)
Introduce `E _ _ _ H X t A _ s ε q W Y _ hW b a n L u₀ ρ hu hi hρ hloc`. Use `choose T hT hx idx w hidx hfr htri using fun j : {x : W // ((q : ℕ) : W.residueField x) = 0} => hloc j.1 j.2`. Establish `hev : ∀ {U : W.Opens} (hU : IsAffineOpen U) {R : Type} [CommRing R] (x : Sp R ⟶ W) (h : ⊤ ≤ x ⁻¹ᵁ U), spMap (GlobalTheory.Points.valMap x U h).hom ≫ hU.fromSpec = x` using `fun hU R _ x h => GlobalTheory.Points.specMap_valMap_fromSpec hU x h`. Establish `hevb : ∀ j {R : Type} [CommRing R] (x : Sp R ⟶ W) (h : ⊤ ≤ x ⁻¹ᵁ T j), x ≫ b = spMap (GlobalTheory.Points.valMap x (T j) h).hom ≫ (hT j).fromSpec ≫ b` using `fun j R _ x h => (congrArg (· ≫ b) (hev (hT j) x h).symm).trans (Category.assoc _ _ _)`. Use `⟨_, T, fun m j => idx j m, fun j R _ x h m => spMap (dualMap (GlobalTheory.Points.valMap x (T j) h).hom) ≫ w j m, fun x h => ⟨⟨x, h⟩, hx _⟩, fun m j => hidx j m, fun j R _ x h m => ?_, fun j R R' _ _ ψ x h h' m => ?_, fun j R _ x h => ?_, fun j R _ x h ψ hψ => ?_, fun j j' R _ x …` and prove the remaining obligations.

Rewrite using `[hevb j x h]`. Conclude with `locFr_tan (hfr j) _ m`. Establish `e : (GlobalTheory.Points.valMap (spMap ψ ≫ x) (T j) h').hom = ψ.comp (GlobalTheory.Points.valMap x (T j) h).hom` using `RingHom.ext fun f => by`. Rewrite using `[← GlobalTheory.Points.valR_eq, GlobalTheory.Points.valR_spMap_comp ψ x _ h, GlobalTheory.Points.valR_eq x _ h]`. Both sides reduce to the same expression.

Use `beta_reduce`. Rewrite using `[e, GlobalTheory.LineNorm.Chart.dual_comp]`. Take `⟨N, e, u, he, hb⟩` from `(hfr j).1`. Rewrite using `[hevb j x h]`. Conclude with `⟨N, e, fun i => spMap (dualMap (GlobalTheory.Points.valMap x (T j) h).hom) ≫ u i, fun m => by simp only [he], fun i => GlobalTheory.LieMet.isTan_map _ rfl (hb.1 i), hb.2 R _⟩`.

Rewrite `hψ` using `[← Category.assoc]`. Rewrite `hψ`, the goal using `[hevb j x h]`. Conclude with `(hfr j).2 R _ ψ hψ`. Establish `hU : IsAffineOpen (T j ⊓ T j')` using `(hT j).inf (hT j')`. Establish `hg : genericPoint W ∈ T j ⊓ T j'` using `⟨gen_mem (hx j), gen_mem (hx j')⟩`.

Establish `hxU : ⊤ ≤ x ⁻¹ᵁ (T j ⊓ T j')` using `fun z hz => ⟨h hz, h' hz⟩`. Establish `hres : ∀ k, T j ⊓ T j' ≤ T k → ∀ hk : ⊤ ≤ x ⁻¹ᵁ T k, ∃ α : Γ(W, T k) →+* Γ(W, T j ⊓ T j'), spMap α ≫ (hT k).fromSpec = hU.fromSpec ∧ (fnOf _ hg).comp α = fnOf (T k) (gen_mem (hx k)) ∧ (GlobalTheory.Points.valMap x _ hxU).hom.comp α = (GlobalTheory.Points.valMap x _ hk).hom` using `fun k e hk => ⟨(W.presheaf.map (homOfLE e).op).hom, (hT k).map_fromSpec hU _, RingHom.ext fun f => fnOf_resG e hg f, congrArg CommRingCat.Hom.hom (GlobalTheory.Points.res_valMap x e hxU hk)⟩`. Take `⟨α, h1, h2, h3⟩` from `hres j inf_le_left h`. Take `⟨α', h1', h2', h3'⟩` from `hres j' inf_le_right h'`. Establish `e1 : spMap α ≫ (hT j).fromSpec ≫ b = hU.fromSpec ≫ b` using `(Category.assoc _ _ _).symm.trans (congrArg (· ≫ b) h1)`.

Establish `e1' : spMap α' ≫ (hT j').fromSpec ≫ b = hU.fromSpec ≫ b` using `(Category.assoc _ _ _).symm.trans (congrArg (· ≫ b) h1')`. Take `⟨C, hC⟩` from `locFr_comb (hfr j) (hfr j') α α' (e1'.trans e1.symm) m`. Use `replace hC : IsCombAtG t (S := Γ(W, T j ⊓ T j')) (hU.fromSpec ≫ b) _ _ _ := e1 ▸ hC`. Establish `eg : ∀ {Z : Scheme.{0}} (c : W ⟶ Z), spMap (fnOf _ hg) ≫ hU.fromSpec ≫ c = GlobalTheory.CurveRootGeometry.genPt W ≫ c` using `fun c => (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) (gen_fromSpec hU hg))`. Establish `ex : ∀ {Z : Scheme.{0}} (c : W ⟶ Z), spMap (GlobalTheory.Points.valMap x _ hxU).hom ≫ hU.fromSpec ≫ c = x ≫ c` using `fun c => (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) (hev hU x hxU))`.

Establish `ha : ⊤ ≤ (hU.fromSpec ≫ a) ⁻¹ᵁ ((L m).U (idx j m) ⊓ (L m).U (idx j' m))` using `fun z hz =>`. Establish `hz' : hU.fromSpec z ∈ T j ⊓ T j'` using `hU.fromSpec_preimage_self.ge hz`. Use the proof step `⟨hidx j m hz'.1, hidx j' m hz'.2⟩`. Establish `hval` using `fun (S : Type) [CommRing S] (σ : Γ(W, T j ⊓ T j') →+* S) => GlobalTheory.Points.valR_spMap_comp (C := Γ(W, T j ⊓ T j')) σ (hU.fromSpec ≫ a) _ ha ((L m).g (idx j m) (idx j' m)).val`. Establish `key` using `tri_comb (y := hU.fromSpec ≫ b) (fnOf _ hg) (fnOf_injective _ hg) (u := u₀) (eg b ▸ hu) (eg b ▸ hi) (w := fun l => spMap (dualMap α) ≫ w j l) (w' := fun l => spMap (dualMap α') ≫ w j' l) (fun l => (ρ l (idx j l))⁻¹.ne_zero) (by simp only [GlobalTheory.LineNorm.Chart.dual_comp, h2 …`.

Establish `h5` using `hρ m (idx j m) (idx j' m) (eg a ▸ fun z hz => ha trivial)`. Rewrite using `[← hval, eg a]`. Simplify using `only [Units.val_inv_eq_inv_val]`. Establish `h6` using `(ρ m (idx j m)).ne_zero`. Establish `h7` using `(ρ m (idx j' m)).ne_zero`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[h5])`. Establish `h8` using `GlobalTheory.LatDRFree.comb_map t (GlobalTheory.Points.valMap x _ hxU).hom hC`. Simplify using `only [GlobalTheory.LineNorm.Chart.dual_comp, h3, h3'] at h8`. Use `⟨fun i => (GlobalTheory.Points.valMap x _ hxU).hom (C i), ?_, fun l hl => ?_, ex b ▸ h8⟩` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[key.1, ← hval, ex a]`. Use `beta_reduce`. Rewrite using `[key.2 l hl, map_zero]`.
-/
theorem UpperTheory.tangent_sections_line_bundle_units :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] (s : X ⟶ Sp A) (ε : 𝓞 E →+* A) (q : ℕ) (W Y : Scheme.{0}) [IsIntegral W], W.IsSeparated → ∀ (b : W ⟶ X) (a : W ⟶ Y) (n : ℕ) (L : ℕ → LB Y) (u₀ : Fin n → (Sp (DualNumber W.functionField) ⟶ t.G.left)) (ρ : ∀ m : Fin n, (L m).ι → W.functionFieldˣ), (∀ m, IsTanAtG t (GlobalTheory.CurveRootGeometry.genPt W ≫ b) (u₀ m)) → IsIndep t (GlobalTheory.CurveRootGeometry.genPt W ≫ b) u₀ → (∀ (m : Fin n) (i j : (L m).ι), ⊤ ≤ (GlobalTheory.CurveRootGeometry.genPt W ≫ a) ⁻¹ᵁ ((L m).U i ⊓ (L m).U j) → (ρ m i : W.functionField) = valR (GlobalTheory.CurveRootGeometry.genPt W ≫ a) _ ((L m).g i j).val * ρ m j) → (∀ x : W, ((q : ℕ) : W.residueField x) = 0 → ∃ (T : W.Opens) (hT : IsAffineOpen T) (hx : x ∈ T) (idx : ∀ m : Fin n, (L m).ι) (w : Fin n → (Sp (DualNumber Γ(W, T)) ⟶ t.G.left)), (∀ m : Fin n, T ≤ a ⁻¹ᵁ (L m).U (idx m)) ∧ GlobalTheory.TriFlag.IsLocFr t s ε (R := Γ(W, T)) (hT.fromSpec ≫ b) w ∧ GlobalTheory.TriFlag.IsTriOf t (GlobalTheory.CurveRootGeometry.genPt W ≫ b) u₀ (fun m => (((ρ m (idx m))⁻¹ : W.functionFieldˣ) : W.functionField)) (fun m => spMap (dualMap (fnOf T (gen_mem hx))) ≫ w m)) → GlobalTheory.TriFlag.TriFrames t s ε q b a n L := by
  intro E _ _ _ H X t A _ s ε q W Y _ hW b a n L u₀ ρ hu hi hρ hloc
  choose T hT hx idx w hidx hfr htri using fun j : {x : W // ((q : ℕ) : W.residueField x) = 0} => hloc j.1 j.2
  have hev : ∀ {U : W.Opens} (hU : IsAffineOpen U) {R : Type} [CommRing R] (x : Sp R ⟶ W) (h : ⊤ ≤ x ⁻¹ᵁ U),
      spMap (GlobalTheory.Points.valMap x U h).hom ≫ hU.fromSpec = x :=
    fun hU R _ x h => GlobalTheory.Points.specMap_valMap_fromSpec hU x h
  have hevb : ∀ j {R : Type} [CommRing R] (x : Sp R ⟶ W) (h : ⊤ ≤ x ⁻¹ᵁ T j),
      x ≫ b = spMap (GlobalTheory.Points.valMap x (T j) h).hom ≫ (hT j).fromSpec ≫ b :=
    fun j R _ x h => (congrArg (· ≫ b) (hev (hT j) x h).symm).trans (Category.assoc _ _ _)
  refine ⟨_, T, fun m j => idx j m, fun j R _ x h m => spMap (dualMap (GlobalTheory.Points.valMap x (T j) h).hom) ≫ w j m,
    fun x h => ⟨⟨x, h⟩, hx _⟩, fun m j => hidx j m, fun j R _ x h m => ?_, fun j R R' _ _ ψ x h h' m => ?_,
    fun j R _ x h => ?_, fun j R _ x h ψ hψ => ?_, fun j j' R _ x h h' m => ?_⟩
  · rw [hevb j x h]
    exact locFr_tan (hfr j) _ m
  · have e : (GlobalTheory.Points.valMap (spMap ψ ≫ x) (T j) h').hom = ψ.comp (GlobalTheory.Points.valMap x (T j) h).hom :=
      RingHom.ext fun f => by
        rw [← GlobalTheory.Points.valR_eq, GlobalTheory.Points.valR_spMap_comp ψ x _ h, GlobalTheory.Points.valR_eq x _ h]; rfl
    beta_reduce
    rw [e, GlobalTheory.LineNorm.Chart.dual_comp]
  · obtain ⟨N, e, u, he, hb⟩ := (hfr j).1
    rw [hevb j x h]
    exact ⟨N, e, fun i => spMap (dualMap (GlobalTheory.Points.valMap x (T j) h).hom) ≫ u i, fun m => by simp only [he],
      fun i => GlobalTheory.LieMet.isTan_map _ rfl (hb.1 i), hb.2 R _⟩
  · rw [← Category.assoc] at hψ
    rw [hevb j x h] at hψ ⊢
    exact (hfr j).2 R _ ψ hψ
  · have hU : IsAffineOpen (T j ⊓ T j') := (hT j).inf (hT j')
    have hg : genericPoint W ∈ T j ⊓ T j' := ⟨gen_mem (hx j), gen_mem (hx j')⟩
    have hxU : ⊤ ≤ x ⁻¹ᵁ (T j ⊓ T j') := fun z hz => ⟨h hz, h' hz⟩
    have hres : ∀ k, T j ⊓ T j' ≤ T k → ∀ hk : ⊤ ≤ x ⁻¹ᵁ T k, ∃ α : Γ(W, T k) →+* Γ(W, T j ⊓ T j'),
        spMap α ≫ (hT k).fromSpec = hU.fromSpec ∧ (fnOf _ hg).comp α = fnOf (T k) (gen_mem (hx k)) ∧
        (GlobalTheory.Points.valMap x _ hxU).hom.comp α = (GlobalTheory.Points.valMap x _ hk).hom := fun k e hk =>
      ⟨(W.presheaf.map (homOfLE e).op).hom, (hT k).map_fromSpec hU _, RingHom.ext fun f => fnOf_resG e hg f,
        congrArg CommRingCat.Hom.hom (GlobalTheory.Points.res_valMap x e hxU hk)⟩
    obtain ⟨α, h1, h2, h3⟩ := hres j inf_le_left h
    obtain ⟨α', h1', h2', h3'⟩ := hres j' inf_le_right h'
    have e1 : spMap α ≫ (hT j).fromSpec ≫ b = hU.fromSpec ≫ b :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ b) h1)
    have e1' : spMap α' ≫ (hT j').fromSpec ≫ b = hU.fromSpec ≫ b :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ b) h1')
    obtain ⟨C, hC⟩ := locFr_comb (hfr j) (hfr j') α α' (e1'.trans e1.symm) m
    replace hC : IsCombAtG t (S := Γ(W, T j ⊓ T j')) (hU.fromSpec ≫ b) _ _ _ := e1 ▸ hC
    have eg : ∀ {Z : Scheme.{0}} (c : W ⟶ Z), spMap (fnOf _ hg) ≫ hU.fromSpec ≫ c = GlobalTheory.CurveRootGeometry.genPt W ≫ c :=
      fun c => (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) (gen_fromSpec hU hg))
    have ex : ∀ {Z : Scheme.{0}} (c : W ⟶ Z), spMap (GlobalTheory.Points.valMap x _ hxU).hom ≫ hU.fromSpec ≫ c = x ≫ c :=
      fun c => (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) (hev hU x hxU))
    have ha : ⊤ ≤ (hU.fromSpec ≫ a) ⁻¹ᵁ ((L m).U (idx j m) ⊓ (L m).U (idx j' m)) := fun z hz =>
      have hz' : hU.fromSpec z ∈ T j ⊓ T j' := hU.fromSpec_preimage_self.ge hz
      ⟨hidx j m hz'.1, hidx j' m hz'.2⟩
    have hval := fun (S : Type) [CommRing S] (σ : Γ(W, T j ⊓ T j') →+* S) =>
      GlobalTheory.Points.valR_spMap_comp (C := Γ(W, T j ⊓ T j')) σ (hU.fromSpec ≫ a) _ ha ((L m).g (idx j m) (idx j' m)).val
    have key := tri_comb (y := hU.fromSpec ≫ b) (fnOf _ hg) (fnOf_injective _ hg) (u := u₀) (eg b ▸ hu) (eg b ▸ hi)
      (w := fun l => spMap (dualMap α) ≫ w j l) (w' := fun l => spMap (dualMap α') ≫ w j' l)
      (fun l => (ρ l (idx j l))⁻¹.ne_zero)
      (by simp only [GlobalTheory.LineNorm.Chart.dual_comp, h2]; exact eg b ▸ htri j)
      (by simp only [GlobalTheory.LineNorm.Chart.dual_comp, h2']; exact eg b ▸ htri j') hC
      (g := valR (A := Γ(W, T j ⊓ T j')) (hU.fromSpec ≫ a) _ ((L m).g (idx j m) (idx j' m)).val) (by
        have h5 := hρ m (idx j m) (idx j' m) (eg a ▸ fun z hz => ha trivial)
        rw [← hval, eg a]
        simp only [Units.val_inv_eq_inv_val]
        have h6 := (ρ m (idx j m)).ne_zero
        have h7 := (ρ m (idx j' m)).ne_zero
        field_simp
        rw [h5])
    have h8 := GlobalTheory.LatDRFree.comb_map t (GlobalTheory.Points.valMap x _ hxU).hom hC
    simp only [GlobalTheory.LineNorm.Chart.dual_comp, h3, h3'] at h8
    refine ⟨fun i => (GlobalTheory.Points.valMap x _ hxU).hom (C i), ?_, fun l hl => ?_, ex b ▸ h8⟩
    · beta_reduce
      rw [key.1, ← hval, ex a]
    · beta_reduce
      rw [key.2 l hl, map_zero]
