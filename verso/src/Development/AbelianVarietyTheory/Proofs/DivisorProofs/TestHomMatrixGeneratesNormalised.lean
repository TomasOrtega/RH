import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixMatCond

/- English proof (translation)
Set `Y0 : Over (Sp Rg)` to `Over.mk (φ ≫ A.hom)`. Establish `w1 : ψ ≫ (topS Rg ⊗ A).hom = Y0.hom` using `by show _ = φ ≫ A.hom`. Rewrite using `[← h, Category.assoc, Over.w (snd (topS Rg) A)]`. Establish `w2 : (φ ≫ θ A) ≫ (topS Rg ⊗ A).hom = Y0.hom` using `by show _ = φ ≫ A.hom`. Rewrite using `[Category.assoc, ← Over.w (snd (topS Rg) A), ← Category.assoc (θ A), θ_snd, Category.id_comp]`.

Set `u : Y0 ⟶ topS Rg ⊗ A` to `Over.homMk ψ w1`. Set `v : Y0 ⟶ topS Rg ⊗ A` to `Over.homMk (φ ≫ θ A) w2`. Establish `: u = v`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Use extensionality with `haveI : Mono (topS Rg).hom := by dsimp [topS, overRes]; infer_instance`.

Rewrite using `[← cancel_mono (topS Rg).hom]`. Simplify using `only [Over.comp_left, Category.assoc, Over.w]`. Apply the tactic sequence `try exact w1.trans w2.symm`. Use `ext`. Simplify using `only [Over.comp_left, u, v, Over.homMk_left, Category.assoc, θ_snd, Category.comp_id, h]`.

Conclude with `congrArg CommaMorphism.left this`.
-/
theorem eq_θ {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) {Y : Scheme.{0}} (φ : Y ⟶ A.left)
    (ψ : Y ⟶ (topS Rg ⊗ A).left) (h : ψ ≫ (snd (topS Rg) A).left = φ) : ψ = φ ≫ θ A := by
  let Y0 : Over (Sp Rg) := Over.mk (φ ≫ A.hom)
  have w1 : ψ ≫ (topS Rg ⊗ A).hom = Y0.hom := by
    show _ = φ ≫ A.hom
    rw [← h, Category.assoc, Over.w (snd (topS Rg) A)]
  have w2 : (φ ≫ θ A) ≫ (topS Rg ⊗ A).hom = Y0.hom := by
    show _ = φ ≫ A.hom
    rw [Category.assoc, ← Over.w (snd (topS Rg) A), ← Category.assoc (θ A), θ_snd, Category.id_comp]
  let u : Y0 ⟶ topS Rg ⊗ A := Over.homMk ψ w1
  let v : Y0 ⟶ topS Rg ⊗ A := Over.homMk (φ ≫ θ A) w2
  have : u = v := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      haveI : Mono (topS Rg).hom := by dsimp [topS, overRes]; infer_instance
      rw [← cancel_mono (topS Rg).hom]
      simp only [Over.comp_left, Category.assoc, Over.w]
      try exact w1.trans w2.symm
    · ext
      simp only [Over.comp_left, u, v, Over.homMk_left, Category.assoc, θ_snd, Category.comp_id, h]
  exact congrArg CommaMorphism.left this

/- English proof (translation)
Simplify using `only [gs_eq f y U h, map_sum]`.
-/
theorem gs_sum' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {n : ℕ}
    (a : Fin n → Γ(X, U)) : gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

/- English proof (translation)
Simplify using `only [gs_eq f y U h, map_pow]`.
-/
theorem gs_pow' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by
  simp only [gs_eq f y U h, map_pow]

/- English proof (translation)
Rewrite using `[← gs_pull t g z U h, gs_stalkMap t z _ h, gs_pull (𝟙 _) g (t z) U h, Category.id_comp]`.
-/
theorem gs_comp_stalk {X Y Z : Scheme.{0}} (t : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (t z) ∈ U)
    (f : Γ(X, U)) : gs (t ≫ g) z U f = (t.stalkMap z).hom (gs g (t z) U f) := by
  rw [← gs_pull t g z U h, gs_stalkMap t z _ h, gs_pull (𝟙 _) g (t z) U h, Category.id_comp]

/- English proof (translation)
The claim follows from `(gs_pull (𝟙 _) f y ⊤ trivial a).trans (by rw [Category.id_comp])`.
-/
theorem gs_appTop' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (a : Γ(X, ⊤)) :
    gs (𝟙 Y) y ⊤ (f.appTop.hom a) = gs f y ⊤ a :=
  (gs_pull (𝟙 _) f y ⊤ trivial a).trans (by rw [Category.id_comp])

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun i => by rw [Fin.fin_one_eq_zero i]; exact h⟩`.
-/
theorem mem_wchart_one {X Y : Scheme.{0}} (L : LB X) (m : Y ⟶ X) (j : Fin 1 → L.ι) (y : Y) :
    y ∈ LB.wchart L (fun _ : Fin 1 => m) j ↔ m y ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun i => by rw [Fin.fin_one_eq_zero i]; exact h⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩`.
-/
theorem mem_wchart_unit {X Y : Scheme.{0}} (L : LB X) (m : Y ⟶ X) (q : L.ι) (y : Y) :
    y ∈ LB.wchart L (fun _ : PUnit => m) (fun _ => q) ↔ m y ∈ L.U q :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

/- English proof (translation)
Rewrite using `[← e]`. Both sides reduce to the same expression.
-/
theorem app_of_comp {X Y Z : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (x : X) :
    g (f x) = h x := by
  rw [← e]; rfl

/- English proof (translation)
The claim follows from `(mem_wchart_one L (f ≫ g) j ((𝟙 Z) z)).2 ((mem_wchart_one L g j (f z)).1 h)`.
-/
theorem mem_wchart_comp {X Y Z : Scheme.{0}} (L : LB X) (f : Z ⟶ Y) (g : Y ⟶ X) (j : Fin 1 → L.ι) (z : Z)
    (h : f z ∈ LB.wchart L (fun _ : Fin 1 => g) j) : (𝟙 Z) z ∈ LB.wchart L (fun _ : Fin 1 => f ≫ g) j :=
  (mem_wchart_one L (f ≫ g) j ((𝟙 Z) z)).2 ((mem_wchart_one L g j (f z)).1 h)

end GlobalTheory.HomFixMatCond

namespace GlobalTheory.HomFixMatCond

/- English proof (translation)
Introduce `Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB R _ t A' B' _ _ φA' φB' Φ' c hL hM hcov hvA hvB hT hMat`. Take `⟨hpA, hpB, hΦ, -⟩` from `hT`. Take `⟨ψA, ψB, α, hA, hB, -, hnorm, hmat⟩` from `hMat`. Take `rfl` from `eq_θ A φA' ψA hA`. Take `rfl` from `eq_θ B φB' ψB hB`.

Establish `key : ∀ {Z : Scheme.{0}} (r : Z ⟶ A'.left) (z : Z) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)) (_ : r z ∈ (isoLB (L` using `L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p) (j : Fin mB), gs (r ≫ Φ'.left ≫ φB' ≫ θ B) z ((LPow B M (k : ℤ) (topS Rg)).U p.1) ((bB j).f p.1) = gs r z _ (α.s p).val * ∑ i, gs (r ≫ A'.hom) z ⊤ (c i j) * gs (r ≫ φA' ≫ θ A) z ((LPow A L (k : ℤ) (topS Rg)).U p.2) ((bA i).f p.2) := …`. Introduce `Z r z p hz j`. Establish `e` using `congrArg (gs r z _) (hmat j p)`. Use `erw [gs_appLE _ _ _ _ r z hz, gs_mul r z _ hz, gs_sum' r z _ hz] at e`. Use `Eq.trans ?_ (e.trans ?_)` and prove the remaining obligations.

Both sides reduce to the same expression. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[gs_mul r z _ hz]`. Use `erw [gs_appLE _ _ _ _ r z hz, gs_appLE _ _ _ _ r z hz]`.

Apply the tactic sequence `all_goals rfl`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z q hq`. Establish `hz : (Φ'.left ≫ φB' ≫ θ B) z ∈ ⨆ j, nonzeroLocus (bB j)` using `by rw [hcov]; trivial`. Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 hz`.

Unfold `nonzeroLocus at hj`. Take `⟨kk, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 hj`. Establish `hkU` using `(topS Rg ⊗ B).left.basicOpen_le _ hk`. Establish `hzU : (𝟙 A'.left) z ∈ (isoLB (L` using `L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U (kk, q) := ⟨mem_wchart_comp _ _ _ _ _ hkU, mem_wchart_comp _ _ _ _ _ hq⟩`. Establish `e` using `key (𝟙 _) z (kk, q) hzU j`.

Simplify using `only [Category.id_comp] at e`. Use `⟨j, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (gs (Φ'.left ≫ φB' ≫ θ B) z _ ((bB j).f kk))`. Rewrite using `[gs_eq _ _ _ hkU]`. Establish `: z ∈ A'.left.basicOpen (((Φ'.left ≫ φB' ≫ θ B).app _).hom ((bB j).f kk))`.

Rewrite using `[← Scheme.preimage_basicOpen]`. Conclude with `hk`. Conclude with `(Scheme.mem_basicOpen _ _ _ _).1 this`. Rewrite `hu` using `[e]`. Conclude with `isUnit_of_mul_isUnit_right hu`.

Introduce `z q kk hq hk j j'`. Establish `hzU : (𝟙 A'.left) z ∈ (isoLB (L` using `L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U (kk, q) := ⟨mem_wchart_comp _ _ _ _ _ hk, mem_wchart_comp _ _ _ _ _ hq⟩`. Establish `e1` using `key (𝟙 _) z (kk, q) hzU j`. Establish `e2` using `key (𝟙 _) z (kk, q) hzU j'`. Simplify using `only [Category.id_comp] at e1 e2`.

Establish `hc : ∀ j, comb bA (φA' ≫ θ A) A'.hom c z q j = ∑ i, gs A'.hom z ⊤ (c i j) * gs (φA' ≫ θ A) z ((LPow A L (k : ℤ) (topS Rg)).U q) ((bA i).f q)` using `fun _ => rfl`. Rewrite using `[hc, hc, e1, e2]`. Expand and normalize the polynomial expressions, which then agree. Introduce `j`. Apply `fn_ext` to reduce the goal to its premises.

Introduce `x _`. Take `⟨qA, hqA⟩` from `exists_chart hL (eSec A (t x))`. Take `⟨qB, hqB⟩` from `exists_chart hM (eSec B (t x))`. Establish `F2 : zeroPt A' ≫ φA' = t ≫ eSec A` using `GlobalTheory.PolBaseChange.eSec_comm hpA`. Establish `F3 : zeroPt A' ≫ Φ'.left ≫ φB' = t ≫ eSec B`.

Establish `h0 : zeroPt A' ≫ Φ'.left = zeroPt B'` using `by show η[A'].left ≫ Φ'.left = η[B'].left`. Rewrite using `[← Over.comp_left, IsMonHom.one_hom]`. Rewrite using `[← Category.assoc, h0]`. Conclude with `GlobalTheory.PolBaseChange.eSec_comm hpB`. Establish `F1 : zeroPt A' ≫ A'.hom = 𝟙 _` using `Over.w η[A']`.

Establish `GA : zeroPt A' ≫ φA' ≫ θ A = t ≫ eSec A ≫ θ A` using `by rw [reassoc_of% F2]`. Establish `GB : zeroPt A' ≫ Φ'.left ≫ φB' ≫ θ B = t ≫ eSec B ≫ θ B` using `by rw [reassoc_of% F3]`. Set `p : (Fin 1 → M.ι) × (Fin 1 → L.ι)` to `(fun _ => qB, fun _ => qA)`. Establish `hx0 : zeroPt A' x ∈ (isoLB (L` using `L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p := by`. Use `⟨(mem_wchart_one _ _ _ _).2 ?_, (mem_wchart_one _ _ _ _).2 ?_⟩` and prove the remaining obligations.

Rewrite using `[app_of_comp (f := zeroPt A') (g := (Φ'.left ≫ φB' ≫ θ B) ≫ (snd (topS Rg) B).left) (h := t ≫ eSec B) (by simp only [Category.assoc, θ_snd, Category.comp_id]; exact F3)]`. Conclude with `hqB`. Rewrite using `[app_of_comp (f := zeroPt A') (g := (φA' ≫ θ A) ≫ (snd (topS Rg) A).left) (h := t ≫ eSec A) (by simp only [Category.assoc, θ_snd, Category.comp_id]; exact F2)]`. Conclude with `hqA`. Establish `hmemA : (eSec A ≫ θ A) (t x) ∈ (LPow A L (k : ℤ) (topS Rg)).U p.2`.

Use `(mem_wchart_one _ _ _ _).2 ?_` and prove the remaining obligations. Rewrite using `[app_of_comp (f := eSec A ≫ θ A) (g := (snd (topS Rg) A).left) (h := eSec A) (by rw [Category.assoc, θ_snd, Category.comp_id])]`. Conclude with `hqA`. Establish `hmemB : (eSec B ≫ θ B) (t x) ∈ (LPow B M (k : ℤ) (topS Rg)).U p.1`. Use `(mem_wchart_one _ _ _ _).2 ?_` and prove the remaining obligations.

Rewrite using `[app_of_comp (f := eSec B ≫ θ B) (g := (snd (topS Rg) B).left) (h := eSec B) (by rw [Category.assoc, θ_snd, Category.comp_id])]`. Conclude with `hqB`. Establish `hWA : t x ∈ (L.pull (eSec A)).U (fun _ => p.2 0)` using `(mem_wchart_unit _ _ _ _).2 hqA`. Establish `hWB : t x ∈ (M.pull (eSec B)).U (fun _ => p.1 0)` using `(mem_wchart_unit _ _ _ _).2 hqB`. Establish `hIA : ∀ i, gs (t ≫ eSec A ≫ θ A) x ((LPow A L (k : ℤ) (topS Rg)).U p.2) ((bA i).f p.2) = gs t x ⊤ (αA i) * gs t x _ (eA.s (fun _ => qA)).val ^ k`.

Introduce `i`. Rewrite using `[gs_comp_stalk _ _ _ _ hmemA, hvA i (t x) p.2 hmemA, map_mul]`. Use `congr 1`. Conclude with `(gs_stalkMap t x ⊤ trivial _).symm`. Use `show (t.stalkMap x).hom ((gm (𝟙 _) (t x) _ (eA.s _)) ^ k).val = _`.

Rewrite using `[Units.val_pow_eq_pow_val, map_pow, ← gs_unit (𝟙 _) (t x) _ hWA, ← gs_stalkMap t x _ hWA]`. Establish `hIB : gs (t ≫ eSec B ≫ θ B) x ((LPow B M (k : ℤ) (topS Rg)).U p.1) ((bB j).f p.1) = gs t x ⊤ (βB j) * gs t x _ (eB.s (fun _ => qB)).val ^ k`. Rewrite using `[gs_comp_stalk _ _ _ _ hmemB, hvB j (t x) p.1 hmemB, map_mul]`. Use `congr 1`. Conclude with `(gs_stalkMap t x ⊤ trivial _).symm`.

Use `show (t.stalkMap x).hom ((gm (𝟙 _) (t x) _ (eB.s _)) ^ k).val = _`. Rewrite using `[Units.val_pow_eq_pow_val, map_pow, ← gs_unit (𝟙 _) (t x) _ hWB, ← gs_stalkMap t x _ hWB]`. Establish `hxW : (𝟙 (Sp R)) x ∈ (zeroPt A') ⁻¹ᵁ (isoLB (L` using `L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0) := ⟨⟨hx0, hWA⟩, hWB⟩`. Establish `hN : gs (zeroPt A') x _ (α.s p).val * gs t x _ (eA.s (fun _ => qA)).val ^ k = gs t x _ (eB.s (fun _ => qB)).val ^ k`. Establish `e` using `congrArg (gs (𝟙 (Sp R)) x _) (hnorm p)`.

Rewrite `e` using `[gs_mul _ _ _ hxW, gs_pow' _ _ _ hxW, gs_pow' _ _ _ hxW]`. Use `erw [gs_appLE _ _ _ _ _ x hxW, gs_appLE _ _ _ _ _ x hxW, gs_appLE _ _ _ _ _ x hxW] at e`. Simplify using `only [Category.id_comp] at e`. Conclude with `e`. Establish `eK` using `key (zeroPt A') x p hx0 j`.

Rewrite `eK` using `[GA, GB, F1, hIB]`. Simplify using `only [hIA] at eK`. Establish `heb : IsUnit (gs t x _ (eB.s (fun _ => qB)).val)`. Rewrite using `[gs_unit t x _ hWB]`. Conclude with `Units.isUnit _`.

Rewrite using `[gs_appTop', gs_sum' (𝟙 (Sp R)) x ⊤ trivial]`. Simplify using `only [gs_mul (𝟙 (Sp R)) x ⊤ trivial, gs_appTop']`. Apply `(heb.pow k).mul_left_inj.1` to reduce the goal to its premises. Rewrite using `[eK, ← hN, Finset.sum_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem mat_cond : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), L.IsLB → M.IsLB → (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c ∧ GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom (Φ'.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B) c ∧ GlobalTheory.HomFixUniv.Normal t c αA βB := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB R _ t A' B' _ _ φA' φB' Φ' c hL hM hcov hvA hvB hT hMat
  obtain ⟨hpA, hpB, hΦ, -⟩ := hT
  obtain ⟨ψA, ψB, α, hA, hB, -, hnorm, hmat⟩ := hMat
  obtain rfl := eq_θ A φA' ψA hA
  obtain rfl := eq_θ B φB' ψB hB
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ A'.left) (z : Z) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι))
      (_ : r z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p) (j : Fin mB),
      gs (r ≫ Φ'.left ≫ φB' ≫ θ B) z ((LPow B M (k : ℤ) (topS Rg)).U p.1) ((bB j).f p.1) =
        gs r z _ (α.s p).val * ∑ i, gs (r ≫ A'.hom) z ⊤ (c i j) *
          gs (r ≫ φA' ≫ θ A) z ((LPow A L (k : ℤ) (topS Rg)).U p.2) ((bA i).f p.2) := by
    intro Z r z p hz j
    have e := congrArg (gs r z _) (hmat j p)
    erw [gs_appLE _ _ _ _ r z hz, gs_mul r z _ hz, gs_sum' r z _ hz] at e
    refine Eq.trans ?_ (e.trans ?_)
    · rfl
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [gs_mul r z _ hz]
      erw [gs_appLE _ _ _ _ r z hz, gs_appLE _ _ _ _ r z hz]
      all_goals rfl
  refine ⟨?_, ?_, ?_⟩
  · intro z q hq
    have hz : (Φ'.left ≫ φB' ≫ θ B) z ∈ ⨆ j, nonzeroLocus (bB j) := by rw [hcov]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    unfold nonzeroLocus at hj
    obtain ⟨kk, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hj
    have hkU := (topS Rg ⊗ B).left.basicOpen_le _ hk
    have hzU : (𝟙 A'.left) z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U (kk, q) :=
      ⟨mem_wchart_comp _ _ _ _ _ hkU, mem_wchart_comp _ _ _ _ _ hq⟩
    have e := key (𝟙 _) z (kk, q) hzU j
    simp only [Category.id_comp] at e
    refine ⟨j, ?_⟩
    have hu : IsUnit (gs (Φ'.left ≫ φB' ≫ θ B) z _ ((bB j).f kk)) := by
      rw [gs_eq _ _ _ hkU]
      have : z ∈ A'.left.basicOpen (((Φ'.left ≫ φB' ≫ θ B).app _).hom ((bB j).f kk)) := by
        rw [← Scheme.preimage_basicOpen]; exact hk
      exact (Scheme.mem_basicOpen _ _ _ _).1 this
    rw [e] at hu
    exact isUnit_of_mul_isUnit_right hu
  · intro z q kk hq hk j j'
    have hzU : (𝟙 A'.left) z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U (kk, q) :=
      ⟨mem_wchart_comp _ _ _ _ _ hk, mem_wchart_comp _ _ _ _ _ hq⟩
    have e1 := key (𝟙 _) z (kk, q) hzU j
    have e2 := key (𝟙 _) z (kk, q) hzU j'
    simp only [Category.id_comp] at e1 e2
    have hc : ∀ j, comb bA (φA' ≫ θ A) A'.hom c z q j = ∑ i, gs A'.hom z ⊤ (c i j) *
        gs (φA' ≫ θ A) z ((LPow A L (k : ℤ) (topS Rg)).U q) ((bA i).f q) := fun _ => rfl
    rw [hc, hc, e1, e2]
    ring
  · intro j
    apply fn_ext
    intro x _
    obtain ⟨qA, hqA⟩ := exists_chart hL (eSec A (t x))
    obtain ⟨qB, hqB⟩ := exists_chart hM (eSec B (t x))
    have F2 : zeroPt A' ≫ φA' = t ≫ eSec A := GlobalTheory.PolBaseChange.eSec_comm hpA
    have F3 : zeroPt A' ≫ Φ'.left ≫ φB' = t ≫ eSec B := by
      have h0 : zeroPt A' ≫ Φ'.left = zeroPt B' := by
        show η[A'].left ≫ Φ'.left = η[B'].left
        rw [← Over.comp_left, IsMonHom.one_hom]
      rw [← Category.assoc, h0]; exact GlobalTheory.PolBaseChange.eSec_comm hpB
    have F1 : zeroPt A' ≫ A'.hom = 𝟙 _ := Over.w η[A']
    have GA : zeroPt A' ≫ φA' ≫ θ A = t ≫ eSec A ≫ θ A := by rw [reassoc_of% F2]
    have GB : zeroPt A' ≫ Φ'.left ≫ φB' ≫ θ B = t ≫ eSec B ≫ θ B := by rw [reassoc_of% F3]
    let p : (Fin 1 → M.ι) × (Fin 1 → L.ι) := (fun _ => qB, fun _ => qA)
    have hx0 : zeroPt A' x ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p := by
      refine ⟨(mem_wchart_one _ _ _ _).2 ?_, (mem_wchart_one _ _ _ _).2 ?_⟩
      · rw [app_of_comp (f := zeroPt A') (g := (Φ'.left ≫ φB' ≫ θ B) ≫ (snd (topS Rg) B).left)
          (h := t ≫ eSec B) (by simp only [Category.assoc, θ_snd, Category.comp_id]; exact F3)]
        exact hqB
      · rw [app_of_comp (f := zeroPt A') (g := (φA' ≫ θ A) ≫ (snd (topS Rg) A).left)
          (h := t ≫ eSec A) (by simp only [Category.assoc, θ_snd, Category.comp_id]; exact F2)]
        exact hqA
    have hmemA : (eSec A ≫ θ A) (t x) ∈ (LPow A L (k : ℤ) (topS Rg)).U p.2 := by
      refine (mem_wchart_one _ _ _ _).2 ?_
      rw [app_of_comp (f := eSec A ≫ θ A) (g := (snd (topS Rg) A).left) (h := eSec A)
        (by rw [Category.assoc, θ_snd, Category.comp_id])]
      exact hqA
    have hmemB : (eSec B ≫ θ B) (t x) ∈ (LPow B M (k : ℤ) (topS Rg)).U p.1 := by
      refine (mem_wchart_one _ _ _ _).2 ?_
      rw [app_of_comp (f := eSec B ≫ θ B) (g := (snd (topS Rg) B).left) (h := eSec B)
        (by rw [Category.assoc, θ_snd, Category.comp_id])]
      exact hqB
    have hWA : t x ∈ (L.pull (eSec A)).U (fun _ => p.2 0) := (mem_wchart_unit _ _ _ _).2 hqA
    have hWB : t x ∈ (M.pull (eSec B)).U (fun _ => p.1 0) := (mem_wchart_unit _ _ _ _).2 hqB
    have hIA : ∀ i, gs (t ≫ eSec A ≫ θ A) x ((LPow A L (k : ℤ) (topS Rg)).U p.2) ((bA i).f p.2) =
        gs t x ⊤ (αA i) * gs t x _ (eA.s (fun _ => qA)).val ^ k := by
      intro i
      rw [gs_comp_stalk _ _ _ _ hmemA, hvA i (t x) p.2 hmemA, map_mul]
      congr 1
      · exact (gs_stalkMap t x ⊤ trivial _).symm
      · show (t.stalkMap x).hom ((gm (𝟙 _) (t x) _ (eA.s _)) ^ k).val = _
        rw [Units.val_pow_eq_pow_val, map_pow, ← gs_unit (𝟙 _) (t x) _ hWA, ← gs_stalkMap t x _ hWA]
    have hIB : gs (t ≫ eSec B ≫ θ B) x ((LPow B M (k : ℤ) (topS Rg)).U p.1) ((bB j).f p.1) =
        gs t x ⊤ (βB j) * gs t x _ (eB.s (fun _ => qB)).val ^ k := by
      rw [gs_comp_stalk _ _ _ _ hmemB, hvB j (t x) p.1 hmemB, map_mul]
      congr 1
      · exact (gs_stalkMap t x ⊤ trivial _).symm
      · show (t.stalkMap x).hom ((gm (𝟙 _) (t x) _ (eB.s _)) ^ k).val = _
        rw [Units.val_pow_eq_pow_val, map_pow, ← gs_unit (𝟙 _) (t x) _ hWB, ← gs_stalkMap t x _ hWB]
    have hxW : (𝟙 (Sp R)) x ∈ (zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p ⊓
        t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
        t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0) := ⟨⟨hx0, hWA⟩, hWB⟩
    have hN : gs (zeroPt A') x _ (α.s p).val * gs t x _ (eA.s (fun _ => qA)).val ^ k =
        gs t x _ (eB.s (fun _ => qB)).val ^ k := by
      have e := congrArg (gs (𝟙 (Sp R)) x _) (hnorm p)
      rw [gs_mul _ _ _ hxW, gs_pow' _ _ _ hxW, gs_pow' _ _ _ hxW] at e
      erw [gs_appLE _ _ _ _ _ x hxW, gs_appLE _ _ _ _ _ x hxW, gs_appLE _ _ _ _ _ x hxW] at e
      simp only [Category.id_comp] at e
      exact e
    have eK := key (zeroPt A') x p hx0 j
    rw [GA, GB, F1, hIB] at eK
    simp only [hIA] at eK
    have heb : IsUnit (gs t x _ (eB.s (fun _ => qB)).val) := by
      rw [gs_unit t x _ hWB]; exact Units.isUnit _
    rw [gs_appTop', gs_sum' (𝟙 (Sp R)) x ⊤ trivial]
    simp only [gs_mul (𝟙 (Sp R)) x ⊤ trivial, gs_appTop']
    apply (heb.pow k).mul_left_inj.1
    rw [eK, ← hN, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.HomFixMatCond
