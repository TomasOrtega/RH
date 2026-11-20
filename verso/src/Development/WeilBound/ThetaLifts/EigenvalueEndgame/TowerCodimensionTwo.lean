import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use function extensionality and compare the values at `h`. Simplify using `only [Model.I, theta]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]`.
-/
theorem I_trans {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (Φ : Fn F n d) (k : UA σ W.J) :
    M.I om (om (1, k) Φ) = fun h => M.I om Φ (h * k) := by
  funext h
  simp only [Model.I, theta]
  congr 1
  funext g
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

/- English proof (translation)
Use function extensionality and compare the values at `h`. Simplify using `only [Model.I, theta, map_smul, thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left, integral_const_mul]`.
-/
theorem I_smul {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (Φ : Fn F n d) (c : ℂ) :
    M.I om (c • Φ) = c • M.I om Φ := by
  funext h
  simp only [Model.I, theta, map_smul, thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left, integral_const_mul]

section Law

variable {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}

/- English proof (translation)
Introduce `μ 𝓕 h1 h2 h3 x` and use `by simpa only [mul_assoc] using h μ 𝓕 h1 h2 h3 (x * k)`.
-/
theorem isCT_right {f c : UA σ W.J → ℂ} (h : IsCT H' f c) (k : UA σ W.J) : IsCT H' (fun x => f (x * k)) fun x => c (x * k) :=
  fun μ 𝓕 h1 h2 h3 x => by simpa only [mul_assoc] using h μ 𝓕 h1 h2 h3 (x * k)

/- English proof (translation)
Introduce `t m hm x` and use `by simpa only [mul_assoc] using h t m hm (x * k)`.
-/
theorem hasLaw_right {χ : Chr F E} {z : ℝ} {T : UA σ W.J → ℂ} (h : HasLaw W₁ H' χ z T) (k : UA σ W.J) :
    HasLaw W₁ H' χ z fun x => T (x * k) := fun t m hm x => by simpa only [mul_assoc] using h t m hm (x * k)

/- English proof (translation)
Introduce `_ _ _ _` and use `by simp`.
-/
theorem hasLaw_zero (χ : Chr F E) (z : ℝ) : HasLaw W₁ H' χ z (0 : UA σ W.J → ℂ) := fun _ _ _ _ => by simp

/- English proof (translation)
Introduce `t m hm x` and use `by simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h t m hm x, h' t m hm x]; ring`.
-/
theorem hasLaw_sub {χ : Chr F E} {z : ℝ} {T T' : UA σ W.J → ℂ} (h : HasLaw W₁ H' χ z T) (h' : HasLaw W₁ H' χ z T') (c : ℂ) :
    HasLaw W₁ H' χ z (T - c • T') := fun t m hm x => by
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h t m hm x, h' t m hm x]; ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.sub (h'.1.const_smul c), fun γ hγ x => by simp only [Pi.sub_apply, Pi.smul_apply, h.2 γ hγ x, h'.2 γ hγ x]⟩`.
-/
theorem isAut_sub {f g : UA σ W.J → ℂ} (h : IsAut f) (h' : IsAut g) (c : ℂ) : IsAut (f - c • g) :=
  ⟨h.1.sub (h'.1.const_smul c), fun γ hγ x => by simp only [Pi.sub_apply, Pi.smul_apply, h.2 γ hγ x, h'.2 γ hγ x]⟩

/- English proof (translation)
Take `⟨d₁, W₁, H, c, h1, h2, h3⟩` from `h`. Conclude with `⟨d₁, W₁, H, _, h1, isCT_right h2 k, hasLaw_right h3 k⟩`.
-/
theorem pure_right {χ : Chr F E} {z : ℝ} {f : UA σ W.J → ℂ} (h : Pure W χ z f) (k : UA σ W.J) : Pure W χ z fun x => f (x * k) := by
  obtain ⟨d₁, W₁, H, c, h1, h2, h3⟩ := h
  exact ⟨d₁, W₁, H, _, h1, isCT_right h2 k, hasLaw_right h3 k⟩

/- English proof (translation)
Use function extensionality and compare the values at `x`. Take `⟨u, hu, t, m, h₁, l, k, hk, hm, hl, rfl⟩` from `(hI F E σ B d d₁ W W₁ H' i₀ i₁ r s hB hW hH).2 x`. Rewrite using `[hN u hu, hT t m hm, h0 h₁ l hl k hk, mul_zero, Pi.zero_apply]`.
-/
theorem comp_zero (hI : Iwa) {B : Base F E} {i₀ i₁ r s : ℕ} (hB : B.IsGood σ) (hW : W.IsSkew σ B r s)
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) {χ : Chr F E} {z : ℝ} {T : UA σ W.J → ℂ} (hT : HasLaw W₁ H' χ z T)
    (hN : ∀ u ∈ unip σ W H', ∀ h, T (u * h) = T h)
    (h0 : ∀ (h₁ : UA σ W₁.J) l, IsLevi H' 1 h₁ l → ∀ k ∈ FinK σ B W, T (l * k) = 0) : T = 0 := by
  funext x
  obtain ⟨u, hu, t, m, h₁, l, k, hk, hm, hl, rfl⟩ := (hI F E σ B d d₁ W W₁ H' i₀ i₁ r s hB hW hH).2 x
  rw [hN u hu, hT t m hm, h0 h₁ l hl k hk, mul_zero, Pi.zero_apply]

end Law

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

/- English proof (translation)
Establish `: (a' : ℝ) < a` using `by exact_mod_cast hT.geo.lt`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem half_ne (hT : IsTriple B G X om om') : ((a' : ℝ) / 2) ≠ (a : ℝ) / 2 := by
  have : (a' : ℝ) < a := by exact_mod_cast hT.geo.lt
  linarith

/- English proof (translation)
Take `⟨Φ, hΦ, Φ', hΦ', rfl⟩` from `hf`. Take `⟨h1, h2⟩` from `hA F E σ B a a' G X om om' hT`. Simplify using `using isAut_sub (h1 Φ hΦ) (h2 Φ' hΦ') 1`.
-/
theorem sig_isAut (hA : IAut) (hT : IsTriple B G X om om') {f : UA σ G.W.J → ℂ} (hf : f ∈ Sig B G om om') : IsAut (W := G.W) f := by
  obtain ⟨Φ, hΦ, Φ', hΦ', rfl⟩ := hf
  obtain ⟨h1, h2⟩ := hA F E σ B a a' G X om om' hT
  simpa using isAut_sub (h1 Φ hΦ) (h2 Φ' hΦ') 1

/- English proof (translation)
Establish `hc` using `h1 F E σ B a a' G X om om' hT d₁ W₁ H' hH f hf h0`. Take `⟨i1, i2⟩` from `h2 F E σ B a a' G X om om' hT f hf hc`. Take `⟨j1, j2⟩` from `h3 F E σ B a a' G X om om' hT f hf hc`. Use `h4 F E σ B a a' G X om om' hT f hf ?_ ?_` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos G.p with hp | hp` into its components or cases.

Conclude with `j1 hp (by omega)`. Conclude with `i1 hp`. Break down `Nat.eq_zero_or_pos G.q with hq | hq` into its components or cases. Conclude with `j2 hq (by omega)`. Conclude with `i2 hq`.
-/
theorem zero_of_line (h1 : CuspOfLine) (h2 : OrthIso) (h3 : OrthAn) (h4 : PerpZero) (hT : IsTriple B G X om om')
    (hy : 1 ≤ G.p ∨ 1 ≤ G.q) {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} (hH : IsPlane σ H' G.W W₁)
    {f : UA σ G.W.J → ℂ} (hf : f ∈ Sig B G om om') (h0 : IsCT H' f 0) : f = 0 := by
  have hc := h1 F E σ B a a' G X om om' hT d₁ W₁ H' hH f hf h0
  obtain ⟨i1, i2⟩ := h2 F E σ B a a' G X om om' hT f hf hc
  obtain ⟨j1, j2⟩ := h3 F E σ B a a' G X om om' hT f hf hc
  refine h4 F E σ B a a' G X om om' hT f hf ?_ ?_
  · rcases Nat.eq_zero_or_pos G.p with hp | hp
    · exact j1 hp (by omega)
    · exact i1 hp
  · rcases Nat.eq_zero_or_pos G.q with hq | hq
    · exact j2 hq (by omega)
    · exact i2 hq

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `using congrFun h (x * k⁻¹)`.
-/
theorem zero_of_right {W : Spc F E a} {f : UA σ W.J → ℂ} {k : UA σ W.J} (h : (fun x => f (x * k)) = 0) : f = 0 := by
  funext x
  simpa using congrFun h (x * k⁻¹)

structure Leaves : Prop where
  iwa : Iwa
  ctBasic : CTBasic
  lineMove : LineMove
  iAut : IAut
  matchStab : MatchStab
  sigRe : SigRe
  towerCodimensionTwo : TowerCodimensionTwo
  alphaZero : AlphaZero
  betaZero : BetaZero
  alphaLow : AlphaLow
  twoStep : TwoStep
  cuspOfLine : CuspOfLine
  orthIso : OrthIso
  orthAn : OrthAn
  perpZero : PerpZero

/- English proof (translation)
Establish `hpl` using `(L.iwa F E σ B _ _ _ _ H' _ _ _ _ hT.base hT.geo.hW hH).1`. Take `⟨c, hc, hl⟩` from `L.lineMove F E σ B _ _ G.W W₁ H' _ _ X.α _ f hT.base hT.geo.hW hpl (sig_isAut L.iAut hT hf) hP`. Conclude with `⟨c, by simpa using hc, hl, hasLaw_zero _ _⟩`.
-/
theorem split_of_pure (L : Leaves) (hT : IsTriple B G X om om') {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} {i₀ i₁ : ℕ}
    (hH : H'.IsAdapted σ B G.W W₁ i₀ i₁) {f : UA σ G.W.J → ℂ} (hf : f ∈ Sig B G om om') (hP : Pure G.W X.α ((a' : ℝ) / 2) f) :
    ∃ c, Split2 W₁ H' X f c 0 := by
  have hpl := (L.iwa F E σ B _ _ _ _ H' _ _ _ _ hT.base hT.geo.hW hH).1
  obtain ⟨c, hc, hl⟩ := L.lineMove F E σ B _ _ G.W W₁ H' _ _ X.α _ f hT.base hT.geo.hW hpl (sig_isAut L.iAut hT hf) hP
  exact ⟨c, by simpa using hc, hl, hasLaw_zero _ _⟩

/- English proof (translation)
Take `⟨c, hs⟩` from `split_of_pure L hT hH hf hP`. Establish `h0` using `L.alphaZero F E σ B a a' G X om om' hT hp hq d₁ W₁ H' i₀ i₁ r s hH hW₁ f hf c 0 hs`. Establish `hpl` using `(L.iwa F E σ B _ _ _ _ H' _ _ _ _ hT.base hT.geo.hW hH).1`. Conclude with `zero_of_line L.cuspOfLine L.orthIso L.orthAn L.perpZero hT (Or.inr hq) hpl hf (by simpa [h0] using hs.1)`.
-/
theorem baseB (L : Leaves) (hT : IsTriple B G X om om') (hp : G.p = 0) (hq : 1 ≤ G.q) {d₁ : ℕ} {W₁ : Spc F E d₁}
    {H' : Plane E (a + a') d₁} {i₀ i₁ r s : ℕ} (hH : H'.IsAdapted σ B G.W W₁ i₀ i₁) (hW₁ : W₁.IsSkew σ B r s)
    {f : UA σ G.W.J → ℂ} (hf : f ∈ Sig B G om om') (hP : Pure G.W X.α ((a' : ℝ) / 2) f) : f = 0 := by
  obtain ⟨c, hs⟩ := split_of_pure L hT hH hf hP
  have h0 := L.alphaZero F E σ B a a' G X om om' hT hp hq d₁ W₁ H' i₀ i₁ r s hH hW₁ f hf c 0 hs
  have hpl := (L.iwa F E σ B _ _ _ _ H' _ _ _ _ hT.base hT.geo.hW hH).1
  exact zero_of_line L.cuspOfLine L.orthIso L.orthAn L.perpZero hT (Or.inr hq) hpl hf (by simpa [h0] using hs.1)

/- English proof (translation)
Take `⟨c, hs⟩` from `split_of_pure L hT hC.hH' hf hP`. Establish `hpl` using `(L.iwa F E σ B _ _ _ _ H' _ _ _ _ hT.base hT.geo.hW hC.hH').1`. Establish `hlow` using `L.alphaLow F E σ B b a' G G₁ X om om' om₁ om₁' H H' hT hT₁ hC hq f hf c 0 hs`. Establish `h0 : c = 0`. Use `comp_zero L.iwa hT.base hT.geo.hW hC.hH' hs.2.1 (fun u hu h => ?_) fun h₁ l hl' k hk => ?_` and prove the remaining obligations.

Conclude with `((L.ctBasic F E σ B _ _ _ _ H' _ _ hT.base hT.geo.hW hpl).2 _ c 0 _ _ _ _ (sig_isAut L.iAut hT hf) (half_ne hT) hs.1 hs.2.1 hs.2.2 u hu h).1`. Take `⟨f₁, hf₁, hL⟩` from `hlow k hk`. Use `ih f₁ hf₁ (L.twoStep F E σ B b a' G G₁ X om om' om₁ om₁' H H' hT hT₁ hC hq f hf c hs hlow k hk f₁ hf₁ hL)` as an intermediate fact. Rewrite using `[← hL h₁ l hl', this, Pi.zero_apply]`. Conclude with `zero_of_line L.cuspOfLine L.orthIso L.orthAn L.perpZero hT (Or.inr hq) hpl hf (by simpa [h0] using hs.1)`.
-/
theorem stepB (L : Leaves) {b : ℕ} {G : Geo σ (b + 2) a'} {G₁ : Geo σ b a'} {om om' om₁ om₁'} {H H'} (hT : IsTriple B G X om om')
    (hT₁ : IsTriple B G₁ X om₁ om₁') (hC : PlaneRemovalConfiguration B G G₁ H H') (hq : 1 ≤ G.q)
    (ih : ∀ f₁ ∈ Sig B G₁ om₁ om₁', Pure G₁.W X.α ((a' : ℝ) / 2) f₁ → f₁ = 0)
    {f : UA σ G.W.J → ℂ} (hf : f ∈ Sig B G om om') (hP : Pure G.W X.α ((a' : ℝ) / 2) f) : f = 0 := by
  obtain ⟨c, hs⟩ := split_of_pure L hT hC.hH' hf hP
  have hpl := (L.iwa F E σ B _ _ _ _ H' _ _ _ _ hT.base hT.geo.hW hC.hH').1
  have hlow := L.alphaLow F E σ B b a' G G₁ X om om' om₁ om₁' H H' hT hT₁ hC hq f hf c 0 hs
  have h0 : c = 0 := by
    refine comp_zero L.iwa hT.base hT.geo.hW hC.hH' hs.2.1 (fun u hu h => ?_) fun h₁ l hl' k hk => ?_
    · exact ((L.ctBasic F E σ B _ _ _ _ H' _ _ hT.base hT.geo.hW hpl).2 _ c 0 _ _ _ _ (sig_isAut L.iAut hT hf)
        (half_ne hT) hs.1 hs.2.1 hs.2.2 u hu h).1
    · obtain ⟨f₁, hf₁, hL⟩ := hlow k hk
      have := ih f₁ hf₁ (L.twoStep F E σ B b a' G G₁ X om om' om₁ om₁' H H' hT hT₁ hC hq f hf c hs hlow k hk f₁ hf₁ hL)
      rw [← hL h₁ l hl', this, Pi.zero_apply]
  exact zero_of_line L.cuspOfLine L.orthIso L.orthAn L.perpZero hT (Or.inr hq) hpl hf (by simpa [h0] using hs.1)

/- English proof (translation)
Take `⟨d₁, W₁, K, c, h1, h2, h3⟩` from `h`. Conclude with `⟨d₁, W₁, K, c, ⟨h1.rank, h1.xx, h1.yy, h1.xy, h1.orth, h1.gram, h1.nondeg⟩, h2, h3⟩`.
-/
theorem pure_reS {d : ℕ} {W W' : Spc F E d} {χ : Chr F E} {z : ℝ} {f : UA σ W.J → ℂ} (h : Pure W χ z f) :
    Pure (reS W W') χ z f := by
  obtain ⟨d₁, W₁, K, c, h1, h2, h3⟩ := h
  exact ⟨d₁, W₁, K, c, ⟨h1.rank, h1.xx, h1.yy, h1.xy, h1.orth, h1.gram, h1.nondeg⟩, h2, h3⟩

/- English proof (translation)
Proceed by induction on `p with`. Consider the case `zero`. Introduce `a a' G om om' hT hp hq f hf hP`. Take `⟨b, rfl⟩ : ∃ b, a' = b + 2` from `⟨a' - 2, by have := hT.geo.aBig; omega⟩`. Take `⟨V, V', W, hT', G₁, H, H', hC, om₁, om₁', hT₁⟩` from `hB F E σ B a b G X om om' hT hq`.

Take `⟨h₀, hh⟩` from `L.sigRe F E σ B a _ G X om om' hT V V' W hT'`. Conclude with `zero_of_right (baseB (G := reG G V V' W) L hT' hp hq hC.hH' hT₁.geo.hW (hh f hf) (pure_reS (pure_right hP h₀)))`. Consider the case `succ p ih`. Introduce `a a' G om om' hT hp hq f hf hP`. Take `⟨b, rfl⟩ : ∃ b, a = b + 2` from `⟨a - 2, by have := hT.geo.aBig; have := hT.geo.lt; omega⟩`.

Take `⟨V, V', W, hT', G₁, H, H', hC, om₁, om₁', hT₁⟩` from `L.towerCodimensionTwo F E σ B b a' G X om om' hT (by omega)`. Take `⟨h₀, hh⟩` from `L.sigRe F E σ B _ a' G X om om' hT V V' W hT'`. Establish `e1 : G₁.p + 1 = G.p` using `hC.ep`. Establish `e2 : G₁.q = G.q` using `hC.eq`. Conclude with `zero_of_right (stepB (G := reG G V V' W) L hT' hT₁ hC hq (ih b a' G₁ om₁ om₁' hT₁ (by omega) (by omega)) (hh f hf) (pure_reS (pure_right hP h₀)))`.
-/
theorem sumB (L : Leaves) (hB : TowerB) (B : Base F E) (X : Chars F E) (p : ℕ) : ∀ (a a' : ℕ) (G : Geo σ a a') om om',
    IsTriple B G X om om' → G.p = p → 1 ≤ G.q → ∀ f ∈ Sig B G om om', Pure G.W X.α ((a' : ℝ) / 2) f → f = 0 := by
  induction p with
  | zero =>
    intro a a' G om om' hT hp hq f hf hP
    obtain ⟨b, rfl⟩ : ∃ b, a' = b + 2 := ⟨a' - 2, by have := hT.geo.aBig; omega⟩
    obtain ⟨V, V', W, hT', G₁, H, H', hC, om₁, om₁', hT₁⟩ := hB F E σ B a b G X om om' hT hq
    obtain ⟨h₀, hh⟩ := L.sigRe F E σ B a _ G X om om' hT V V' W hT'
    exact zero_of_right (baseB (G := reG G V V' W) L hT' hp hq hC.hH' hT₁.geo.hW (hh f hf) (pure_reS (pure_right hP h₀)))
  | succ p ih =>
    intro a a' G om om' hT hp hq f hf hP
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by have := hT.geo.aBig; have := hT.geo.lt; omega⟩
    obtain ⟨V, V', W, hT', G₁, H, H', hC, om₁, om₁', hT₁⟩ := L.towerCodimensionTwo F E σ B b a' G X om om' hT (by omega)
    obtain ⟨h₀, hh⟩ := L.sigRe F E σ B _ a' G X om om' hT V V' W hT'
    have e1 : G₁.p + 1 = G.p := hC.ep
    have e2 : G₁.q = G.q := hC.eq
    exact zero_of_right (stepB (G := reG G V V' W) L hT' hT₁ hC hq
      (ih b a' G₁ om₁ om₁' hT₁ (by omega) (by omega)) (hh f hf) (pure_reS (pure_right hP h₀)))

/- English proof (translation)
Establish `hT` using `hm.triple`. Take `⟨p1, p2, -⟩` from `(hM F E σ B a a' G X om om' R Rf hm).2.2 Φ Φ' hΦ' hP`. Take `⟨s1, s2⟩` from `hS F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH`. Take `⟨⟨fa, fb⟩, h1, -⟩` from `s1 Φ p1`. Take `⟨⟨fa', fb'⟩, h2, -⟩` from `s2 Φ' ⟨p2, hΦ'⟩`.

Take `⟨a1, a2⟩` from `L.iAut F E σ B a a' G X om om' hT`. Establish `hpl` using `(L.iwa F E σ B _ _ _ _ H' _ _ _ _ hT.base hT.geo.hW hH).1`. Use `⟨⟨Φ, p1, c • Φ', Submodule.smul_mem _ c ⟨p2, hΦ'⟩, by rw [I_smul]⟩, fa, fb, fa', fb', h1, h2, ?_, hasLaw_sub h1.2.1 h2.2.1 c, hasLaw_sub h1.2.2 h2.2.2 c⟩` and prove the remaining obligations. Use `(L.ctBasic F E σ B _ _ _ _ H' _ _ hT.base hT.geo.hW hpl).1 _ _ _ _ c (a1 Φ p1) (a2 Φ' ⟨p2, hΦ'⟩) h1.1 h2.1` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [smul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem diff_data (L : Leaves) (hS : SplitEx) (hM : MatchEx) {R : RealMaps F a a'} {Rf : FinMaps F a a'}
    (hm : IsMatched B G X om om' R Rf) {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} {i₀ i₁ : ℕ}
    (hH : H'.IsAdapted σ B G.W W₁ i₀ i₁) (c : ℂ) {Φ Φ'} (hΦ' : Φ' ∈ G.M'.So B.ψ B.τ₁) (hP : PolMatch B G X R Rf Φ Φ') :
    G.M.I om Φ - c • G.M'.I om' Φ' ∈ Sig B G om om' ∧ ∃ fa fb fa' fb', Split2 W₁ H' X (G.M.I om Φ) fa fb ∧
      Split2 W₁ H' X (G.M'.I om' Φ') fa' fb' ∧ Split2 W₁ H' X (G.M.I om Φ - c • G.M'.I om' Φ') (fa - c • fa') (fb - c • fb') := by
  have hT := hm.triple
  obtain ⟨p1, p2, -⟩ := (hM F E σ B a a' G X om om' R Rf hm).2.2 Φ Φ' hΦ' hP
  obtain ⟨s1, s2⟩ := hS F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  obtain ⟨⟨fa, fb⟩, h1, -⟩ := s1 Φ p1
  obtain ⟨⟨fa', fb'⟩, h2, -⟩ := s2 Φ' ⟨p2, hΦ'⟩
  obtain ⟨a1, a2⟩ := L.iAut F E σ B a a' G X om om' hT
  have hpl := (L.iwa F E σ B _ _ _ _ H' _ _ _ _ hT.base hT.geo.hW hH).1
  refine ⟨⟨Φ, p1, c • Φ', Submodule.smul_mem _ c ⟨p2, hΦ'⟩, by rw [I_smul]⟩, fa, fb, fa', fb', h1, h2, ?_,
    hasLaw_sub h1.2.1 h2.2.1 c, hasLaw_sub h1.2.2 h2.2.2 c⟩
  have := (L.ctBasic F E σ B _ _ _ _ H' _ _ hT.base hT.geo.hW hpl).1 _ _ _ _ c (a1 Φ p1) (a2 Φ' ⟨p2, hΦ'⟩) h1.1 h2.1
  convert this using 1
  simp only [smul_add]
  abel

/- English proof (translation)
Rewrite using `[I_trans]`. Conclude with `⟨isCT_right h.1 k, hasLaw_right h.2.1 k, hasLaw_right h.2.2 k⟩`.
-/
theorem split_trans {n : ℕ} {Y : Spc F E n} (M : Model σ Y G.W) (o : Rep σ Y G.W) {d₁ : ℕ} {W₁ : Spc F E d₁}
    {H' : Plane E (a + a') d₁} {Φ fa fb} (h : Split2 W₁ H' X (M.I o Φ) fa fb) (k : UA σ G.W.J) :
    Split2 W₁ H' X (M.I o (o (1, k) Φ)) (fun x => fa (x * k)) fun x => fb (x * k) := by
  rw [I_trans]
  exact ⟨isCT_right h.1 k, hasLaw_right h.2.1 k, hasLaw_right h.2.2 k⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' R Rf hm hq d₁ W₁ H' i₀ i₁ hH c hc Φ Φ' hΦ' hP`. Establish `hT` using `hm.triple`. Take `⟨hf, fa, fb, fa', fb', h1, h2, h3⟩` from `diff_data L hS hM hm hH c hΦ' hP`. Establish `hpl` using `(L.iwa F E σ B _ _ _ _ H' _ _ _ _ hT.base hT.geo.hW hH).1`. Establish `h0 : fb - c • fb' = 0`.

Use `comp_zero L.iwa hT.base hT.geo.hW hH h3.2.2 (fun u hu h => ?_) fun h₁ l hl k hk => ?_` and prove the remaining obligations. Conclude with `((L.ctBasic F E σ B _ _ _ _ H' _ _ hT.base hT.geo.hW hpl).2 _ _ _ _ _ _ _ (sig_isAut L.iAut hT hf) (half_ne hT) h3.1 h3.2.1 h3.2.2 u hu h).2`. Take `⟨m1, m2⟩` from `L.matchStab F E σ B a a' G X om om' R Rf hm k hk Φ Φ' hΦ' hP`. Use `hc _ _ m1 m2 _ _ _ _ (split_trans G.M om h1 k) (split_trans G.M' om' h2 k) h₁ l hl` as an intermediate fact. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`.

Conclude with `sub_eq_zero.2 this`. Establish `hz` using `sumB L hB B X G.p a a' G om om' hT rfl hq _ hf ⟨d₁, W₁, H', _, hpl, by simpa [h0] using h3.1, h3.2.1⟩`. Introduce `h`. Conclude with `sub_eq_zero.1 (congrFun hz h)`.
-/
theorem endB_of (L : Leaves) (hB : TowerB) (hS : SplitEx) (hM : MatchEx) : EndB := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm hq d₁ W₁ H' i₀ i₁ hH c hc Φ Φ' hΦ' hP
  have hT := hm.triple
  obtain ⟨hf, fa, fb, fa', fb', h1, h2, h3⟩ := diff_data L hS hM hm hH c hΦ' hP
  have hpl := (L.iwa F E σ B _ _ _ _ H' _ _ _ _ hT.base hT.geo.hW hH).1
  have h0 : fb - c • fb' = 0 := by
    refine comp_zero L.iwa hT.base hT.geo.hW hH h3.2.2 (fun u hu h => ?_) fun h₁ l hl k hk => ?_
    · exact ((L.ctBasic F E σ B _ _ _ _ H' _ _ hT.base hT.geo.hW hpl).2 _ _ _ _ _ _ _ (sig_isAut L.iAut hT hf)
        (half_ne hT) h3.1 h3.2.1 h3.2.2 u hu h).2
    · obtain ⟨m1, m2⟩ := L.matchStab F E σ B a a' G X om om' R Rf hm k hk Φ Φ' hΦ' hP
      have := hc _ _ m1 m2 _ _ _ _ (split_trans G.M om h1 k) (split_trans G.M' om' h2 k) h₁ l hl
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact sub_eq_zero.2 this
  have hz := sumB L hB B X G.p a a' G om om' hT rfl hq _ hf
    ⟨d₁, W₁, H', _, hpl, by simpa [h0] using h3.1, h3.2.1⟩
  intro h
  exact sub_eq_zero.1 (congrFun hz h)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' R Rf hm hq hp d₁ W₁ H' i₀ i₁ hH c hc Φ Φ' hΦ' hP`. Establish `hT` using `hm.triple`. Take `⟨hf, fa, fb, fa', fb', h1, h2, h3⟩` from `diff_data L hS hM hm hH c hΦ' hP`. Establish `hpl` using `(L.iwa F E σ B _ _ _ _ H' _ _ _ _ hT.base hT.geo.hW hH).1`. Establish `h0 : fa - c • fa' = 0`.

Use `comp_zero L.iwa hT.base hT.geo.hW hH h3.2.1 (fun u hu h => ?_) fun h₁ l hl k hk => ?_` and prove the remaining obligations. Conclude with `((L.ctBasic F E σ B _ _ _ _ H' _ _ hT.base hT.geo.hW hpl).2 _ _ _ _ _ _ _ (sig_isAut L.iAut hT hf) (half_ne hT) h3.1 h3.2.1 h3.2.2 u hu h).1`. Take `⟨m1, m2⟩` from `L.matchStab F E σ B a a' G X om om' R Rf hm k hk Φ Φ' hΦ' hP`. Use `hc _ _ m1 m2 _ _ _ _ (split_trans G.M om h1 k) (split_trans G.M' om' h2 k) h₁ l hl` as an intermediate fact. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`.

Conclude with `sub_eq_zero.2 this`. Establish `h0'` using `L.betaZero F E σ B a a' G X om om' hT hq hp d₁ W₁ H' i₀ i₁ hH _ hf _ _ h3`. Establish `hz` using `zero_of_line L.cuspOfLine L.orthIso L.orthAn L.perpZero hT (Or.inl hp) hpl hf (by simpa [h0, h0'] using h3.1)`. Introduce `h`. Conclude with `sub_eq_zero.1 (congrFun hz h)`.
-/
theorem endA_of (L : Leaves) (hS : SplitEx) (hM : MatchEx) : EndA := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm hq hp d₁ W₁ H' i₀ i₁ hH c hc Φ Φ' hΦ' hP
  have hT := hm.triple
  obtain ⟨hf, fa, fb, fa', fb', h1, h2, h3⟩ := diff_data L hS hM hm hH c hΦ' hP
  have hpl := (L.iwa F E σ B _ _ _ _ H' _ _ _ _ hT.base hT.geo.hW hH).1
  have h0 : fa - c • fa' = 0 := by
    refine comp_zero L.iwa hT.base hT.geo.hW hH h3.2.1 (fun u hu h => ?_) fun h₁ l hl k hk => ?_
    · exact ((L.ctBasic F E σ B _ _ _ _ H' _ _ hT.base hT.geo.hW hpl).2 _ _ _ _ _ _ _ (sig_isAut L.iAut hT hf)
        (half_ne hT) h3.1 h3.2.1 h3.2.2 u hu h).1
    · obtain ⟨m1, m2⟩ := L.matchStab F E σ B a a' G X om om' R Rf hm k hk Φ Φ' hΦ' hP
      have := hc _ _ m1 m2 _ _ _ _ (split_trans G.M om h1 k) (split_trans G.M' om' h2 k) h₁ l hl
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact sub_eq_zero.2 this
  have h0' := L.betaZero F E σ B a a' G X om om' hT hq hp d₁ W₁ H' i₀ i₁ hH _ hf _ _ h3
  have hz := zero_of_line L.cuspOfLine L.orthIso L.orthAn L.perpZero hT (Or.inl hp) hpl hf (by simpa [h0, h0'] using h3.1)
  intro h
  exact sub_eq_zero.1 (congrFun hz h)

end PositivityTheory.ThKEnd

end
