import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArcSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

/- English proof (translation)
Substitute `h` using the available equality. Establish `e1 : x = x'` using `Over.OverMorphism.ext hx`. Establish `e2 : y = y'` using `Over.OverMorphism.ext hy`. Substitute `e1 e2` using the available equality. Both sides reduce to the same expression.
-/
theorem mul_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x y : Over.mk a ⟶ G) (x' y' : Over.mk b ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left) :
    (x * y).left = (x' * y').left := by
  subst h
  have e1 : x = x' := Over.OverMorphism.ext hx
  have e2 : y = y' := Over.OverMorphism.ext hy
  subst e1 e2
  rfl

def pushPt {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (w : φ ≫ G.hom = G'.hom ≫ f) {T : Over S'} (x : T ⟶ G') : Over.mk (T.hom ≫ f) ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    show (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, w, ← Category.assoc, Over.w x])

/- English proof (translation)
Use `⟨h'.1.paste_horiz h.1, ?_⟩` and prove the remaining obligations. Introduce `T x y x₀ y₀ hx hy`. Establish `w' : φ' ≫ G'.hom = G''.hom ≫ g` using `h'.1.w`. Establish `h1` using `h'.2 T x y (pushPt w' x) (pushPt w' y) rfl rfl`. Set `T' : Over S'` to `Over.mk (T.hom ≫ g)`.

Set `x₁ : Over.mk (T'.hom ≫ f) ⟶ G` to `Over.homMk x₀.left (by rw [Over.w x₀]; simp [T'])`. Set `y₁ : Over.mk (T'.hom ≫ f) ⟶ G` to `Over.homMk y₀.left (by rw [Over.w y₀]; simp [T'])`. Establish `h2` using `h.2 T' (pushPt w' x) (pushPt w' y) x₁ y₁ (by simp [x₁, pushPt, hx]) (by simp [y₁, pushPt, hy])`. Establish `h3` using `mul_left_congr (G := G) (Category.assoc T.hom g f) x₁ y₁ x₀ y₀ rfl rfl`. Rewrite using `[← h3, h2, h1, Category.assoc]`.
-/
theorem IsGrpPullback.comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (h' : IsGrpPullback G'' G' g φ') (h : IsGrpPullback G' G f φ) : IsGrpPullback G'' G (g ≫ f) (φ' ≫ φ) := by
  refine ⟨h'.1.paste_horiz h.1, ?_⟩
  intro T x y x₀ y₀ hx hy
  have w' : φ' ≫ G'.hom = G''.hom ≫ g := h'.1.w
  have h1 := h'.2 T x y (pushPt w' x) (pushPt w' y) rfl rfl
  let T' : Over S' := Over.mk (T.hom ≫ g)
  let x₁ : Over.mk (T'.hom ≫ f) ⟶ G := Over.homMk x₀.left (by rw [Over.w x₀]; simp [T'])
  let y₁ : Over.mk (T'.hom ≫ f) ⟶ G := Over.homMk y₀.left (by rw [Over.w y₀]; simp [T'])
  have h2 := h.2 T' (pushPt w' x) (pushPt w' y) x₁ y₁ (by simp [x₁, pushPt, hx]) (by simp [y₁, pushPt, hy])
  have h3 := mul_left_congr (G := G) (Category.assoc T.hom g f) x₁ y₁ x₀ y₀ rfl rfl
  rw [← h3, h2, h1, Category.assoc]

/- English proof (translation)
Use `⟨IsPullback.of_right n.1 w h.1, ?_⟩` and prove the remaining obligations. Introduce `T x y x₀ y₀ hx hy`. Establish `hw : φ ≫ G.hom = G'.hom ≫ f` using `h.1.w`. Establish `hn : (φ' ≫ φ) ≫ G.hom = G''.hom ≫ (g ≫ f)` using `n.1.w`. Establish `h1` using `h.2 (Over.mk (T.hom ≫ g)) x₀ y₀ (pushPt hw x₀) (pushPt hw y₀) rfl rfl`.

Establish `h2` using `n.2 T x y (pushPt hn x) (pushPt hn y) rfl rfl`. Establish `h3` using `mul_left_congr (G := G) (Category.assoc T.hom g f) (pushPt hw x₀) (pushPt hw y₀) (pushPt hn x) (pushPt hn y) (by simp [pushPt, hx]) (by simp [pushPt, hy])`. Apply `h.1.hom_ext` to reduce the goal to its premises. Rewrite using `[← h1, h3, h2, Category.assoc]`. Establish `a1` using `Over.w (x₀ * y₀)`.

Establish `a2` using `Over.w (x * y)`. Rewrite using `[a1, Category.assoc, w, ← Category.assoc, a2]`. Both sides reduce to the same expression.
-/
theorem IsGrpPullback.cancel {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (h : IsGrpPullback G' G f φ) (n : IsGrpPullback G'' G (g ≫ f) (φ' ≫ φ)) (w : φ' ≫ G'.hom = G''.hom ≫ g) :
    IsGrpPullback G'' G' g φ' := by
  refine ⟨IsPullback.of_right n.1 w h.1, ?_⟩
  intro T x y x₀ y₀ hx hy
  have hw : φ ≫ G.hom = G'.hom ≫ f := h.1.w
  have hn : (φ' ≫ φ) ≫ G.hom = G''.hom ≫ (g ≫ f) := n.1.w
  have h1 := h.2 (Over.mk (T.hom ≫ g)) x₀ y₀ (pushPt hw x₀) (pushPt hw y₀) rfl rfl
  have h2 := n.2 T x y (pushPt hn x) (pushPt hn y) rfl rfl
  have h3 := mul_left_congr (G := G) (Category.assoc T.hom g f) (pushPt hw x₀) (pushPt hw y₀)
    (pushPt hn x) (pushPt hn y) (by simp [pushPt, hx]) (by simp [pushPt, hy])
  apply h.1.hom_ext
  · rw [← h1, h3, h2, Category.assoc]
  · have a1 := Over.w (x₀ * y₀)
    have a2 := Over.w (x * y)
    rw [a1, Category.assoc, w, ← Category.assoc, a2]
    rfl

/- English proof (translation)
Apply the tactic sequence `have e : (List.finRange 3).filter (· ∈ ({i} : Finset (Fin 3))) = [i] := by fin_cases i <;> decide`. Simplify using `only [psum, e, List.foldr_cons, List.foldr_nil, padd, pzero]`. Use `first`. Consider the case `simp`. Consider the case `exact MonObj.lift_comp_one_right _ _`.
-/
theorem psum_single {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (x : Fin 3 → (T ⟶ G))
    (i : Fin 3) : psum G x {i} = x i := by
  have e : (List.finRange 3).filter (· ∈ ({i} : Finset (Fin 3))) = [i] := by
    fin_cases i <;> decide
  simp only [psum, e, List.foldr_cons, List.foldr_nil, padd, pzero]
  first
    | simp
    | exact MonObj.lift_comp_one_right _ _

/- English proof (translation)
Establish `w : b ≫ (G3 G).hom = a ≫ (G3 G).hom`. Establish `h0` using `h 0`. Establish `k` using `Over.w (x3 G 0)`. Rewrite using `[← k, ← Category.assoc, ← Category.assoc, h0]`. Set `T : Over S` to `Over.mk (a ≫ (G3 G).hom)`.

Set `A : T ⟶ G3 G` to `Over.homMk a rfl`. Set `B : T ⟶ G3 G` to `Over.homMk b w`. Establish `hAB : A = B`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Use `ext`.

Simplify `h 0` using `[A, B, x3]`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Use `ext`. Simplify `h 1` using `[A, B, x3]`. Use `ext`.

Simplify `h 2` using `[A, B, x3]`. Conclude with `congrArg CommaMorphism.left hAB`.
-/
theorem hom_ext_triple {S : Scheme.{0}} (G : Over S) {X : Scheme.{0}} {a b : X ⟶ (G3 G).left}
    (h : ∀ i, a ≫ (x3 G i).left = b ≫ (x3 G i).left) : a = b := by
  have w : b ≫ (G3 G).hom = a ≫ (G3 G).hom := by
    have h0 := h 0
    have k := Over.w (x3 G 0)
    rw [← k, ← Category.assoc, ← Category.assoc, h0]
  let T : Over S := Over.mk (a ≫ (G3 G).hom)
  let A : T ⟶ G3 G := Over.homMk a rfl
  let B : T ⟶ G3 G := Over.homMk b w
  have hAB : A = B := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa [A, B, x3] using h 0
    · apply CartesianMonoidalCategory.hom_ext
      · ext
        simpa [A, B, x3] using h 1
      · ext
        simpa [A, B, x3] using h 2
  exact congrArg CommaMorphism.left hAB

/- English proof (translation)
Establish `k` using `m.psum_comm {i}`. Rewrite `k` using `[psum_single, psum_single]`. Conclude with `k.symm`.
-/
theorem cubeMap_comp_proj_three {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (i : Fin 3) : m.F3 ≫ (x3 G i).left = (x3 G' i).left ≫ m.F := by
  have k := m.psum_comm {i}
  rw [psum_single, psum_single] at k
  exact k.symm

/- English proof (translation)
Introduce `E _ _ _ H S S' S'' t t' t'' f g m m'`. Set `cm : CubeMap t''.G t.G` to `{ F := m'.cm.F ≫ m.cm.F F3 := m'.cm.F3 ≫ m.cm.F3 e := m'.cm.e ≫ m.cm.e e_comm := by`. Rewrite using `[← Category.assoc, m'.cm.e_comm]`. Simplify using `only [Category.assoc, m.cm.e_comm]`. Use `psum_comm := fun I => by`.

Rewrite using `[← Category.assoc, m'.cm.psum_comm I]`. Simplify using `only [Category.assoc, m.cm.psum_comm I] }`. Use `⟨{ cm := cm, cart := IsGrpPullback.comp m'.cart m.cart, base := ?_, act := ?_, lin := ?_ }, rfl⟩` and prove the remaining obligations. Use `show m'.cm.e ≫ m.cm.e = g ≫ f`. Rewrite using `[m'.base, m.base]`.

Introduce `a show _ ≫ (m'.cm.F ≫ m.cm.F) = (m'.cm.F ≫ m.cm.F) ≫ _`. Rewrite using `[← Category.assoc, m'.act a]`. Simplify using `only [Category.assoc, m.act a]`. Conclude with `hC S S' S'' t.G t'.G t''.G m.cm m'.cm cm t.PP t'.PP t''.PP t.cub t'.cub t''.cub rfl rfl rfl m.lin m'.lin`.
-/
theorem sabComp (hC : PullCubCompSt) : SABCompSt := by
  intro E _ _ _ H S S' S'' t t' t'' f g m m'
  let cm : CubeMap t''.G t.G :=
    { F := m'.cm.F ≫ m.cm.F
      F3 := m'.cm.F3 ≫ m.cm.F3
      e := m'.cm.e ≫ m.cm.e
      e_comm := by
        rw [← Category.assoc, m'.cm.e_comm]
        simp only [Category.assoc, m.cm.e_comm]
      psum_comm := fun I => by
        rw [← Category.assoc, m'.cm.psum_comm I]
        simp only [Category.assoc, m.cm.psum_comm I] }
  refine ⟨{ cm := cm, cart := IsGrpPullback.comp m'.cart m.cart, base := ?_, act := ?_, lin := ?_ }, rfl⟩
  · show m'.cm.e ≫ m.cm.e = g ≫ f
    rw [m'.base, m.base]
  · intro a
    show _ ≫ (m'.cm.F ≫ m.cm.F) = (m'.cm.F ≫ m.cm.F) ≫ _
    rw [← Category.assoc, m'.act a]
    simp only [Category.assoc, m.act a]
  · exact hC S S' S'' t.G t'.G t''.G m.cm m'.cm cm t.PP t'.PP t''.PP t.cub t'.cub t''.cub rfl rfl rfl
      m.lin m'.lin

/- English proof (translation)
Introduce `E _ _ _ H S S' S'' t t' t'' f g m n`. Establish `hP` using `m.cart.1`. Establish `hn : n.cm.F ≫ t.G.hom = t''.G.hom ≫ (g ≫ f)` using `n.cart.1.w`. Set `F' : t''.G.left ⟶ t'.G.left` to `hP.lift n.cm.F (t''.G.hom ≫ g) (by rw [hn, Category.assoc])`. Establish `hF1 : F' ≫ m.cm.F = n.cm.F` using `hP.lift_fst _ _ _`.

Establish `hF2 : F' ≫ t'.G.hom = t''.G.hom ≫ g` using `hP.lift_snd _ _ _`. Establish `hF1' : ∀ {Z : Scheme.{0}} (k : t.G.left ⟶ Z), F' ≫ m.cm.F ≫ k = n.cm.F ≫ k`. Introduce `Z k`. Rewrite using `[← Category.assoc, hF1]`. Establish `hF2' : ∀ {Z : Scheme.{0}} (k : S' ⟶ Z), F' ≫ t'.G.hom ≫ k = t''.G.hom ≫ g ≫ k`.

Introduce `Z k`. Rewrite using `[← Category.assoc, hF2, Category.assoc]`. Set `T : Over S'` to `Over.mk ((G3 t''.G).hom ≫ g)`. Set `p : Fin 3 → (T ⟶ t'.G)` to `fun i => Over.homMk ((x3 t''.G i).left ≫ F') (by show ((x3 t''.G i).left ≫ F') ≫ t'.G.hom = (G3 t''.G).hom ≫ g`. Rewrite using `[Category.assoc, hF2, ← Category.assoc, Over.w (x3 t''.G i)])`.

Set `L3 : T ⟶ G3 t'.G` to `lift (p 0) (lift (p 1) (p 2))`. Set `F3' : (G3 t''.G).left ⟶ (G3 t'.G).left` to `L3.left`. Establish `hF3x : ∀ i, F3' ≫ (x3 t'.G i).left = (x3 t''.G i).left ≫ F'`. Introduce `i`. Use `show L3.left ≫ (x3 t'.G i).left = _`.

Rewrite using `[← Over.comp_left]`. Apply the tactic sequence `fin_cases i <;> simp [L3, x3, p]`. Establish `hF3 : F3' ≫ m.cm.F3 = n.cm.F3`. Apply `hom_ext_triple t.G` to reduce the goal to its premises. Introduce `i`.

Rewrite using `[Category.assoc, cubeMap_comp_proj_three m.cm i, ← Category.assoc, hF3x i, Category.assoc, hF1, cubeMap_comp_proj_three n.cm i]`. Establish `hT : F3' ≫ (G3 t'.G).hom = (G3 t''.G).hom ≫ g` using `Over.w L3`. Set `cm : CubeMap t''.G t'.G` to `{ F := F' F3 := F3' e := g e_comm := by`. Apply `hP.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, hF1]`.

Rewrite using `[n.cm.e_comm, m.cm.e_comm, n.base, m.base, Category.assoc]`. Simplify using `only [Category.assoc, hF2]`. Establish `k1` using `Over.w (η[t''.G] : 𝟙_ (Over S'') ⟶ t''.G)`. Establish `k2` using `Over.w (η[t'.G] : 𝟙_ (Over S') ⟶ t'.G)`. Simplify using `only [eSec]`.

Rewrite using `[← Category.assoc, k1, k2]`. Simplify using the standard rewrite rules. Use `psum_comm := fun I => by`. Apply `hP.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, hF1, m.cm.psum_comm I]`.

Rewrite using `[n.cm.psum_comm I, ← Category.assoc, hF3]`. Establish `a1` using `Over.w (psum t''.G (x3 t''.G) I)`. Establish `a2` using `Over.w (psum t'.G (x3 t'.G) I)`. Rewrite using `[Category.assoc, hF2, ← Category.assoc, a1, Category.assoc, a2, hT] }`. Establish `hcart : IsGrpPullback t''.G t.G (g ≫ f) (F' ≫ m.cm.F)`.

Establish `k` using `n.cart`. Rewrite `k` using `[← hF1]`. Conclude with `k`. Use `⟨{ cm := cm, cart := IsGrpPullback.cancel m.cart hcart hF2, base := rfl, act := ?_, lin := ?_ }, hF1.symm⟩` and prove the remaining obligations. Introduce `a show (t''.act.act a).left ≫ F' = F' ≫ (t'.act.act a).left`.

Apply `hP.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, hF1, m.act a, hF1']`. Rewrite using `[n.act a]`. Establish `a1` using `Over.w (t''.act.act a)`. Establish `a2` using `Over.w (t'.act.act a)`.

Rewrite using `[Category.assoc, hF2, ← Category.assoc, a1, Category.assoc, a2, hF2]`. Conclude with `hC S S' S'' t.G t'.G t''.G m.cm cm n.cm t.PP t'.PP t''.PP t.cub t'.cub t''.cub hF1.symm hF3.symm (by show n.cm.e = g ≫ m.cm.e; rw [n.base, m.base]) m.lin n.lin`.
-/
theorem sabCancel (hC : PullCubCancelSt) : SABCancelSt := by
  intro E _ _ _ H S S' S'' t t' t'' f g m n
  have hP := m.cart.1
  have hn : n.cm.F ≫ t.G.hom = t''.G.hom ≫ (g ≫ f) := n.cart.1.w
  let F' : t''.G.left ⟶ t'.G.left := hP.lift n.cm.F (t''.G.hom ≫ g) (by rw [hn, Category.assoc])
  have hF1 : F' ≫ m.cm.F = n.cm.F := hP.lift_fst _ _ _
  have hF2 : F' ≫ t'.G.hom = t''.G.hom ≫ g := hP.lift_snd _ _ _
  have hF1' : ∀ {Z : Scheme.{0}} (k : t.G.left ⟶ Z), F' ≫ m.cm.F ≫ k = n.cm.F ≫ k := by
    intro Z k; rw [← Category.assoc, hF1]
  have hF2' : ∀ {Z : Scheme.{0}} (k : S' ⟶ Z), F' ≫ t'.G.hom ≫ k = t''.G.hom ≫ g ≫ k := by
    intro Z k; rw [← Category.assoc, hF2, Category.assoc]
  let T : Over S' := Over.mk ((G3 t''.G).hom ≫ g)
  let p : Fin 3 → (T ⟶ t'.G) := fun i => Over.homMk ((x3 t''.G i).left ≫ F') (by
      show ((x3 t''.G i).left ≫ F') ≫ t'.G.hom = (G3 t''.G).hom ≫ g
      rw [Category.assoc, hF2, ← Category.assoc, Over.w (x3 t''.G i)])
  let L3 : T ⟶ G3 t'.G := lift (p 0) (lift (p 1) (p 2))
  let F3' : (G3 t''.G).left ⟶ (G3 t'.G).left := L3.left
  have hF3x : ∀ i, F3' ≫ (x3 t'.G i).left = (x3 t''.G i).left ≫ F' := by
    intro i
    show L3.left ≫ (x3 t'.G i).left = _
    rw [← Over.comp_left]
    fin_cases i <;> simp [L3, x3, p]
  have hF3 : F3' ≫ m.cm.F3 = n.cm.F3 := by
    apply hom_ext_triple t.G
    intro i
    rw [Category.assoc, cubeMap_comp_proj_three m.cm i, ← Category.assoc, hF3x i, Category.assoc, hF1,
      cubeMap_comp_proj_three n.cm i]
  have hT : F3' ≫ (G3 t'.G).hom = (G3 t''.G).hom ≫ g := Over.w L3
  let cm : CubeMap t''.G t'.G :=
    { F := F'
      F3 := F3'
      e := g
      e_comm := by
        apply hP.hom_ext
        · simp only [Category.assoc, hF1]
          rw [n.cm.e_comm, m.cm.e_comm, n.base, m.base, Category.assoc]
        · simp only [Category.assoc, hF2]
          have k1 := Over.w (η[t''.G] : 𝟙_ (Over S'') ⟶ t''.G)
          have k2 := Over.w (η[t'.G] : 𝟙_ (Over S') ⟶ t'.G)
          simp only [eSec]
          rw [← Category.assoc, k1, k2]
          simp
      psum_comm := fun I => by
        apply hP.hom_ext
        · simp only [Category.assoc, hF1, m.cm.psum_comm I]
          rw [n.cm.psum_comm I, ← Category.assoc, hF3]
        · have a1 := Over.w (psum t''.G (x3 t''.G) I)
          have a2 := Over.w (psum t'.G (x3 t'.G) I)
          rw [Category.assoc, hF2, ← Category.assoc, a1, Category.assoc, a2, hT] }
  have hcart : IsGrpPullback t''.G t.G (g ≫ f) (F' ≫ m.cm.F) := by
    have k := n.cart
    rw [← hF1] at k
    exact k
  refine ⟨{ cm := cm, cart := IsGrpPullback.cancel m.cart hcart hF2, base := rfl, act := ?_, lin := ?_ },
    hF1.symm⟩
  · intro a
    show (t''.act.act a).left ≫ F' = F' ≫ (t'.act.act a).left
    apply hP.hom_ext
    · simp only [Category.assoc, hF1, m.act a, hF1']
      rw [n.act a]
    · have a1 := Over.w (t''.act.act a)
      have a2 := Over.w (t'.act.act a)
      rw [Category.assoc, hF2, ← Category.assoc, a1, Category.assoc, a2, hF2]
  · exact hC S S' S'' t.G t'.G t''.G m.cm cm n.cm t.PP t'.PP t''.PP t.cub t'.cub t''.cub
      hF1.symm hF3.symm (by show n.cm.e = g ≫ m.cm.e; rw [n.base, m.base]) m.lin n.lin

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
