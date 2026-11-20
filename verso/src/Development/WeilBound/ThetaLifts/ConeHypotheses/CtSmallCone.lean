import Development.WeilBound.ThetaLifts.ConeHypotheses.KeyAOf

noncomputable section

namespace PositivityTheory.ThKG

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

structure Leaves : Prop where
  evZero : EvZero
  evCone : EvCone
  stabEx : StabEx
  towerA : TowerA
  towerB : TowerB
  facNe : FacNe
  matchEx : MatchEx
  leviEx : LeviEx
  polDense : PolDense
  weilConv : WeilConv
  soCont : SoCont
  splitEx : SplitEx
  ctBigZero : CTBigZero
  ctSmallZero : CTSmallZero
  ctBigCone : CTBigCone
  ctSmallCone : CTSmallCone
  anAll : AnAll
  polRe : PolRe
  nonZeroAn : NonZeroAn
  polZero : PolZero
  locA : LocA'
  locB : LocB'
  endA : EndA'
  endB : EndB'
  kReal : KReal
  kFin : KFin

namespace Leaves

variable (L : Leaves)
include L

/- English proof (translation)
The claim follows from `keyB_of L.evZero L.evCone L.stabEx L.ctBigZero L.ctSmallCone L.locB L.leviEx`.
-/
theorem keyB : ∃ e₁ e₂ s, KeyB e₁ e₂ s := keyB_of L.evZero L.evCone L.stabEx L.ctBigZero L.ctSmallCone L.locB L.leviEx

/- English proof (translation)
The claim follows from `keyA_of L.evZero L.evCone L.stabEx L.ctSmallZero L.ctBigCone L.locA L.leviEx L.anAll L.matchEx`.
-/
theorem keyA : ∃ e₁ e₂ s, KeyA e₁ e₂ s :=
  keyA_of L.evZero L.evCone L.stabEx L.ctSmallZero L.ctBigCone L.locA L.leviEx L.anAll L.matchEx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
  {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

/- English proof (translation)
The claim follows from `matching_of_parts L.kReal L.kFin F E σ B a a' G X om om' t`.
-/
theorem matched (t : IsTriple B G X om om') : ∃ R Rf, IsMatched B G X om om' R Rf :=
  matching_of_parts L.kReal L.kFin F E σ B a a' G X om om' t

/- English proof (translation)
Introduce `Φ h` and use `((L.weilConv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) (weilCondV t)).1 Φ h).1`.
-/
theorem conv (t : IsTriple B G X om om') : ∀ Φ ∈ schA F _, G.M.Conv om Φ := fun Φ h =>
  ((L.weilConv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) (weilCondV t)).1 Φ h).1

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Take `⟨Φ, hΦ, hne⟩` from `h`. Use `hne ?_` and prove the remaining obligations. Use `clear hne`.

Establish `key : Φ ∈ schA F _ ∧ G.M.I om Φ = 0`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, -, φ, h1, h2, rfl⟩` from `h`. Take `⟨g, hg, e⟩` from `pure_eq_pureA t.geo.hM φ h1 h2`.

Use `⟨e f ▸ pureA_mem f hg, funext fun x => ?_⟩` and prove the remaining obligations. Establish `hc` using `(L.weilConv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) (weilCondV t)).2 g hg x`. Use `Continuous.ext_on (L.polDense F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t)) hc continuous_const (g := fun _ => (0 : ℂ)) fun f₁ hf₁ => by` as an intermediate fact. Use `hn _ (Submodule.subset_span ⟨f₁, hf₁, φ, h1, h2, rfl⟩)` as an intermediate fact. Rewrite `this` using `[e f₁]`.

Conclude with `congrFun this x`. Rewrite using `[e f]`. Conclude with `congrFun this f`. Consider the case `zero => exact ⟨Submodule.zero_mem _, I_zero _ _⟩`. Consider the case `add Φ Ψ _ _ h1 h2`.

Conclude with `⟨Submodule.add_mem _ h1.1 h2.1, funext fun x => by rw [I_add t.weil (L.conv t) h1.1 h2.1, h1.2, h2.2]; simp⟩`. Consider the case `smul c Φ _ h1 => exact ⟨Submodule.smul_mem _ _ h1.1, funext fun x => by rw [I_smul, h1.2]; simp⟩`. Conclude with `key.2`.
-/
theorem nz_move (t : IsTriple B G X om om') {V V' W} (t₂ : IsTriple B (reG G V V' W) X om om')
    (h : ∃ Φ ∈ PolData B (reG G V V' W).M, G.M.I om Φ ≠ 0) : ∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨Φ, hΦ, hne⟩ := h
  refine hne ?_
  clear hne
  have key : Φ ∈ schA F _ ∧ G.M.I om Φ = 0 := by
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, -, φ, h1, h2, rfl⟩ := h
      obtain ⟨g, hg, e⟩ := pure_eq_pureA t.geo.hM φ h1 h2
      refine ⟨e f ▸ pureA_mem f hg, funext fun x => ?_⟩
      have hc := (L.weilConv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) (weilCondV t)).2 g hg x
      have := Continuous.ext_on (L.polDense F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t)) hc continuous_const (g := fun _ => (0 : ℂ))
        fun f₁ hf₁ => by
          have := hn _ (Submodule.subset_span ⟨f₁, hf₁, φ, h1, h2, rfl⟩)
          rw [e f₁] at this
          exact congrFun this x
      rw [e f]
      exact congrFun this f
    | zero => exact ⟨Submodule.zero_mem _, I_zero _ _⟩
    | add Φ Ψ _ _ h1 h2 =>
      exact ⟨Submodule.add_mem _ h1.1 h2.1, funext fun x => by rw [I_add t.weil (L.conv t) h1.1 h2.1, h1.2, h2.2]; simp⟩
    | smul c Φ _ h1 => exact ⟨Submodule.smul_mem _ _ h1.1, funext fun x => by rw [I_smul, h1.2]; simp⟩
  exact key.2

variable {R : RealMaps F a a'} {Rf : FinMaps F a a'}

/- English proof (translation)
Establish `t` using `m.triple`. Establish `hb` using `t.geo.eBig`. Break down `Nat.eq_zero_or_pos G.q with hq | hq` into its components or cases. Break down `Nat.eq_zero_or_pos G.p with hp | hp` into its components or cases. Conclude with `L.polZero F E σ B a a' G X om om' R Rf m hp hq`.

Take `⟨b, rfl⟩ : ∃ b, a = b + 2` from `⟨a - 2, by omega⟩`. Take `⟨V, V', W, t₂, G₁, H, H', cfg, om₁, om₁', t₁⟩` from `L.towerA F E σ B b a' G X om om' t hq hp`. Take `⟨R₂, Rf₂, m₂⟩` from `L.matched t₂`. Take `⟨R₁, Rf₁, m₁⟩` from `L.matched t₁`. Use `L.polRe F E σ B _ _ G X om om' R Rf m V V' W R₂ Rf₂ m₂ ?_` and prove the remaining obligations.

Take `⟨e₁, e₂, s, key⟩` from `L.keyA`. Take `⟨C, hC, key⟩` from `key F E σ B b a' _ G₁ H H' cfg R₂ R₁`. Establish `hlt : G₁.p + G₁.q < G.p + G.q`. Establish `h1 : G₁.p + 1 = G.p` using `cfg.ep`. Use `cfg.q1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Take `⟨⟨c₁, hc₁, pc₁⟩, -⟩` from `hB F E σ B _ _ G₁ X om₁ om₁' R₁ Rf₁ m₁ hlt`. Take `⟨f1, f2⟩` from `L.facNe F E σ B _ _ G X om om' t e₁ e₂ s H.𝔟 H'.𝔟 (1 - (((b + 2 - a') / 2 : ℕ) : ℤ))`. Use `⟨_, mul_ne_zero (mul_ne_zero (mul_ne_zero hC f1) (f2 ((b + 2 - a') / 2) (by omega))) hc₁, L.endA F E σ B _ _ (reG G V V' W) X om om' R₂ Rf₂ m₂ hq hp hB _ G₁.W H' _ _ cfg.hH' _ ?_⟩` and prove the remaining obligations. Introduce `Φ Φ' so pm fa fb fa' fb' sp sp' h₁ l hl`.

Take `⟨fa'', sp'', rel⟩` from `(key X om om' Rf₂ om₁ om₁' Rf₁ m₂ m₁ hB c₁ pc₁ _ rfl).1 Φ Φ' pm`. Establish `u` using `((L.splitEx F E σ B _ _ (reG G V V' W) X om om' t₂ _ G₁.W H' _ _ cfg.hH').2 Φ' ⟨(polMatch_mem pm).2, so⟩).unique (y₁ := (fa', fb')) (y₂ := (fa'', 0)) sp' sp''`. Take `rfl : fa' = fa''` from `congrArg Prod.fst u`. Conclude with `rel fa fb sp h₁ l hl`. Establish `ha` using `t.geo.aBig`.

Take `⟨b, rfl⟩ : ∃ b, a' = b + 2` from `⟨a' - 2, by omega⟩`. Take `⟨V, V', W, t₂, G₁, H, H', cfg, om₁, om₁', t₁⟩` from `L.towerB F E σ B a b G X om om' t hq`. Take `⟨R₂, Rf₂, m₂⟩` from `L.matched t₂`. Take `⟨R₁, Rf₁, m₁⟩` from `L.matched t₁`. Use `L.polRe F E σ B _ _ G X om om' R Rf m V V' W R₂ Rf₂ m₂ ?_` and prove the remaining obligations.

Take `⟨e₁, e₂, s, key⟩` from `L.keyB`. Take `⟨C, hC, key⟩` from `key F E σ B a b _ G₁ H H' cfg R₂ R₁`. Establish `hlt : G₁.p + G₁.q < G.p + G.q`. Establish `h1 : G₁.p = G.p` using `cfg.ep`. Establish `h2 : G₁.q + 1 = G.q` using `cfg.eq`.

Use linear arithmetic over natural numbers and integers. Take `⟨⟨c₁, hc₁, pc₁⟩, -⟩` from `hB F E σ B _ _ G₁ X om₁ om₁' R₁ Rf₁ m₁ hlt`. Take `⟨f1, f2⟩` from `L.facNe F E σ B _ _ G X om om' t e₁ e₂ s H.𝔟 H'.𝔟 (-(((a - (b + 2)) / 2 : ℕ) : ℤ))`. Establish `f3` using `f2 ((a - (b + 2)) / 2 + 1) (by omega)`. Rewrite `f3` using `[Nat.cast_add, Nat.cast_one]`.

Establish `hk` using `mul_ne_zero (mul_ne_zero hC f1) f3`. Use `⟨_, div_ne_zero hc₁ hk, L.endB F E σ B _ _ (reG G V V' W) X om om' R₂ Rf₂ m₂ hq hB _ G₁.W H' _ _ cfg.hH' _ ?_⟩` and prove the remaining obligations. Introduce `Φ Φ' so pm fa fb fa' fb' sp sp' h₁ l hl`. Use `(key X om om' Rf₂ om₁ om₁' Rf₁ m₂ m₁ hB).1 c₁ pc₁ Φ Φ' so pm fa fb fa' fb' sp sp' h₁ l hl` as an intermediate fact. Rewrite using `[div_mul_eq_mul_div, eq_div_iff hk, mul_comm]`.

Conclude with `this`.
-/
theorem const_of (m : IsMatched B G X om om' R Rf) (hB : Below (G.p + G.q)) : ∃ c, c ≠ 0 ∧ PolConst B G X om om' R Rf c := by
  have t := m.triple
  have hb := t.geo.eBig
  rcases Nat.eq_zero_or_pos G.q with hq | hq
  · rcases Nat.eq_zero_or_pos G.p with hp | hp
    · exact L.polZero F E σ B a a' G X om om' R Rf m hp hq
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    obtain ⟨V, V', W, t₂, G₁, H, H', cfg, om₁, om₁', t₁⟩ := L.towerA F E σ B b a' G X om om' t hq hp
    obtain ⟨R₂, Rf₂, m₂⟩ := L.matched t₂
    obtain ⟨R₁, Rf₁, m₁⟩ := L.matched t₁
    refine L.polRe F E σ B _ _ G X om om' R Rf m V V' W R₂ Rf₂ m₂ ?_
    obtain ⟨e₁, e₂, s, key⟩ := L.keyA
    obtain ⟨C, hC, key⟩ := key F E σ B b a' _ G₁ H H' cfg R₂ R₁
    have hlt : G₁.p + G₁.q < G.p + G.q := by
      have h1 : G₁.p + 1 = G.p := cfg.ep
      have := cfg.q1
      omega
    obtain ⟨⟨c₁, hc₁, pc₁⟩, -⟩ := hB F E σ B _ _ G₁ X om₁ om₁' R₁ Rf₁ m₁ hlt
    obtain ⟨f1, f2⟩ := L.facNe F E σ B _ _ G X om om' t e₁ e₂ s H.𝔟 H'.𝔟 (1 - (((b + 2 - a') / 2 : ℕ) : ℤ))
    refine ⟨_, mul_ne_zero (mul_ne_zero (mul_ne_zero hC f1) (f2 ((b + 2 - a') / 2) (by omega))) hc₁,
      L.endA F E σ B _ _ (reG G V V' W) X om om' R₂ Rf₂ m₂ hq hp hB _ G₁.W H' _ _ cfg.hH' _ ?_⟩
    intro Φ Φ' so pm fa fb fa' fb' sp sp' h₁ l hl
    obtain ⟨fa'', sp'', rel⟩ := (key X om om' Rf₂ om₁ om₁' Rf₁ m₂ m₁ hB c₁ pc₁ _ rfl).1 Φ Φ' pm
    have u := ((L.splitEx F E σ B _ _ (reG G V V' W) X om om' t₂ _ G₁.W H' _ _ cfg.hH').2 Φ' ⟨(polMatch_mem pm).2, so⟩).unique
      (y₁ := (fa', fb')) (y₂ := (fa'', 0)) sp' sp''
    obtain rfl : fa' = fa'' := congrArg Prod.fst u
    exact rel fa fb sp h₁ l hl
  · have ha := t.geo.aBig
    obtain ⟨b, rfl⟩ : ∃ b, a' = b + 2 := ⟨a' - 2, by omega⟩
    obtain ⟨V, V', W, t₂, G₁, H, H', cfg, om₁, om₁', t₁⟩ := L.towerB F E σ B a b G X om om' t hq
    obtain ⟨R₂, Rf₂, m₂⟩ := L.matched t₂
    obtain ⟨R₁, Rf₁, m₁⟩ := L.matched t₁
    refine L.polRe F E σ B _ _ G X om om' R Rf m V V' W R₂ Rf₂ m₂ ?_
    obtain ⟨e₁, e₂, s, key⟩ := L.keyB
    obtain ⟨C, hC, key⟩ := key F E σ B a b _ G₁ H H' cfg R₂ R₁
    have hlt : G₁.p + G₁.q < G.p + G.q := by
      have h1 : G₁.p = G.p := cfg.ep
      have h2 : G₁.q + 1 = G.q := cfg.eq
      omega
    obtain ⟨⟨c₁, hc₁, pc₁⟩, -⟩ := hB F E σ B _ _ G₁ X om₁ om₁' R₁ Rf₁ m₁ hlt
    obtain ⟨f1, f2⟩ := L.facNe F E σ B _ _ G X om om' t e₁ e₂ s H.𝔟 H'.𝔟 (-(((a - (b + 2)) / 2 : ℕ) : ℤ))
    have f3 := f2 ((a - (b + 2)) / 2 + 1) (by omega)
    rw [Nat.cast_add, Nat.cast_one] at f3
    have hk := mul_ne_zero (mul_ne_zero hC f1) f3
    refine ⟨_, div_ne_zero hc₁ hk, L.endB F E σ B _ _ (reG G V V' W) X om om' R₂ Rf₂ m₂ hq hB _ G₁.W H' _ _ cfg.hH' _ ?_⟩
    intro Φ Φ' so pm fa fb fa' fb' sp sp' h₁ l hl
    have := (key X om om' Rf₂ om₁ om₁' Rf₁ m₂ m₁ hB).1 c₁ pc₁ Φ Φ' so pm fa fb fa' fb' sp sp' h₁ l hl
    rw [div_mul_eq_mul_div, eq_div_iff hk, mul_comm]
    exact this

/- English proof (translation)
Establish `ha` using `t.geo.aBig`. Take `⟨b, rfl⟩ : ∃ b, a' = b + 2` from `⟨a' - 2, by omega⟩`. Take `⟨V, V', W, t₂, G₁, H, H', cfg, om₁, om₁', t₁⟩` from `L.towerB F E σ B a b G X om om' t hq`. Take `⟨R₂, Rf₂, m₂⟩` from `L.matched t₂`. Take `⟨R₁, Rf₁, m₁⟩` from `L.matched t₁`.

Take `⟨e₁, e₂, s, key⟩` from `L.keyB`. Take `⟨C, -, key⟩` from `key F E σ B a b _ G₁ H H' cfg R₂ R₁`. Take `⟨Φ, hΦ, h⟩` from `(key X om om' Rf₂ om₁ om₁' Rf₁ m₂ m₁ hB).2`. Use `L.nz_move t t₂ ⟨Φ, hΦ, fun z => ?_⟩` and prove the remaining obligations. Take `⟨_, _, _, hne⟩` from `h 0 0 (by show Split2 _ _ _ (G.M.I om Φ) 0 0`.

Rewrite using `[z]`. Conclude with `⟨fun _ _ _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩)`. Conclude with `hne rfl`.
-/
theorem nzV (t : IsTriple B G X om om') (hq : 1 ≤ G.q) (hB : Below (G.p + G.q)) : ∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0 := by
  have ha := t.geo.aBig
  obtain ⟨b, rfl⟩ : ∃ b, a' = b + 2 := ⟨a' - 2, by omega⟩
  obtain ⟨V, V', W, t₂, G₁, H, H', cfg, om₁, om₁', t₁⟩ := L.towerB F E σ B a b G X om om' t hq
  obtain ⟨R₂, Rf₂, m₂⟩ := L.matched t₂
  obtain ⟨R₁, Rf₁, m₁⟩ := L.matched t₁
  obtain ⟨e₁, e₂, s, key⟩ := L.keyB
  obtain ⟨C, -, key⟩ := key F E σ B a b _ G₁ H H' cfg R₂ R₁
  obtain ⟨Φ, hΦ, h⟩ := (key X om om' Rf₂ om₁ om₁' Rf₁ m₂ m₁ hB).2
  refine L.nz_move t t₂ ⟨Φ, hΦ, fun z => ?_⟩
  obtain ⟨_, _, _, hne⟩ := h 0 0 (by
    show Split2 _ _ _ (G.M.I om Φ) 0 0
    rw [z]
    exact ⟨fun _ _ _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩)
  exact hne rfl

/- English proof (translation)
Take `⟨c, hc, pc⟩` from `L.const_of m hB`. Take `⟨m1, m2, -⟩` from `L.matchEx F E σ B _ _ G X om om' R Rf m`. Use `⟨⟨c, hc, pc⟩, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos G.q with hq | hq` into its components or cases. Take `⟨Φ', ⟨h1, h2⟩, hne⟩` from `(L.nonZeroAn F E σ B _ _ G X om om' m.triple).2 hq`.

Take `⟨Φ, pm⟩` from `m2 Φ' h1`. Take `⟨x, hx⟩` from `Function.ne_iff.1 hne`. Conclude with `⟨⟨Φ, (polMatch_mem pm).1, Function.ne_iff.2 ⟨x, by rw [pc Φ Φ' h2 pm x]; exact mul_ne_zero hc hx⟩⟩, Φ', ⟨h1, h2⟩, hne⟩`. Take `⟨Φ, h1, hne⟩` from `L.nzV m.triple hq hB`. Take `⟨Φ', so, pm⟩` from `m1 Φ h1`.

Use `⟨⟨Φ, h1, hne⟩, Φ', ⟨(polMatch_mem pm).2, so⟩, fun z => hne (funext fun x => ?_)⟩` and prove the remaining obligations. Rewrite using `[pc Φ Φ' so pm x, z]`. Simplify using the standard rewrite rules.
-/
theorem claim_of (m : IsMatched B G X om om' R Rf) (hB : Below (G.p + G.q)) : Claim B G X om om' R Rf := by
  obtain ⟨c, hc, pc⟩ := L.const_of m hB
  obtain ⟨m1, m2, -⟩ := L.matchEx F E σ B _ _ G X om om' R Rf m
  refine ⟨⟨c, hc, pc⟩, ?_⟩
  rcases Nat.eq_zero_or_pos G.q with hq | hq
  · obtain ⟨Φ', ⟨h1, h2⟩, hne⟩ := (L.nonZeroAn F E σ B _ _ G X om om' m.triple).2 hq
    obtain ⟨Φ, pm⟩ := m2 Φ' h1
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
    exact ⟨⟨Φ, (polMatch_mem pm).1, Function.ne_iff.2 ⟨x, by rw [pc Φ Φ' h2 pm x]; exact mul_ne_zero hc hx⟩⟩, Φ', ⟨h1, h2⟩, hne⟩
  · obtain ⟨Φ, h1, hne⟩ := L.nzV m.triple hq hB
    obtain ⟨Φ', so, pm⟩ := m1 Φ h1
    refine ⟨⟨Φ, h1, hne⟩, Φ', ⟨(polMatch_mem pm).2, so⟩, fun z => hne (funext fun x => ?_)⟩
    rw [pc Φ Φ' so pm x, z]
    simp

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)`. Consider the case `succ n ih => exact fun F E _ _ _ _ _ σ B a a' G X om om' R Rf m h => L.claim_of m (ih.mono (by omega))`.
-/
theorem below (n : ℕ) : Below n := by
  induction n with
  | zero => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)
  | succ n ih => exact fun F E _ _ _ _ _ σ B a a' G X om om' R Rf m h => L.claim_of m (ih.mono (by omega))

/- English proof (translation)
The claim follows from `L.claim_of m (L.below _)`.
-/
theorem claim (m : IsMatched B G X om om' R Rf) : Claim B G X om om' R Rf := L.claim_of m (L.below _)

/- English proof (translation)
Introduce `Φ Φ' so pm` and use `h Φ Φ' ((L.matchEx F E σ B _ _ G X om om' R Rf m).2.2 Φ Φ' so pm).2.2`.
-/
theorem polConst_of (m : IsMatched B G X om om' R Rf) {c : ℂ} (h : IsConst B G X om om' R Rf c) : PolConst B G X om om' R Rf c :=
  fun Φ Φ' so pm => h Φ Φ' ((L.matchEx F E σ B _ _ G X om om' R Rf m).2.2 Φ Φ' so pm).2.2

/- English proof (translation)
Introduce and unpack `Φ Φ' ⟨so, k, k', g, f, s, g', f', s', h1, h2, rfl, rfl, h3⟩ x`. Establish `t` using `m.triple`. Establish `l2` using `L.soCont F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t) k' g' f' s' h2 (fun j => (h3 j).1) so x`. Establish `e : ∀ u : Fin k → SInf F _, G.M.I om (∑ i, pureA F (u i) (g i)) x = ∑ i, G.M.I om (pureA F (u i) (g i)) x` using `fun u => I_sum t.weil (L.conv t) _ _ (fun i => pureA_mem _ (h1 i).1) x`. Establish `l1 : Tendsto (fun j => G.M.I om (∑ i, pureA F (s j i) (g i)) x) atTop (𝓝 (G.M.I om (∑ i, pureA F (f i) (g i)) x))`.

Simplify using `only [e]`. Conclude with `tendsto_finset_sum _ fun i _ => (((L.weilConv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) (weilCondV t)).2 _ (h1 i).1 x).tendsto _).comp (h1 i).2`. Conclude with `tendsto_nhds_unique l1 ((l2.const_mul c).congr fun j => (h _ _ (h3 j).1 (h3 j).2 x).symm)`.
-/
theorem isConst_of (m : IsMatched B G X om om' R Rf) {c : ℂ} (h : PolConst B G X om om' R Rf c) : IsConst B G X om om' R Rf c := by
  rintro Φ Φ' ⟨so, k, k', g, f, s, g', f', s', h1, h2, rfl, rfl, h3⟩ x
  have t := m.triple
  have l2 := L.soCont F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t) k' g' f' s' h2 (fun j => (h3 j).1) so x
  have e : ∀ u : Fin k → SInf F _, G.M.I om (∑ i, pureA F (u i) (g i)) x = ∑ i, G.M.I om (pureA F (u i) (g i)) x := fun u =>
    I_sum t.weil (L.conv t) _ _ (fun i => pureA_mem _ (h1 i).1) x
  have l1 : Tendsto (fun j => G.M.I om (∑ i, pureA F (s j i) (g i)) x) atTop (𝓝 (G.M.I om (∑ i, pureA F (f i) (g i)) x)) := by
    simp only [e]
    exact tendsto_finset_sum _ fun i _ =>
      (((L.weilConv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) (weilCondV t)).2 _ (h1 i).1 x).tendsto _).comp (h1 i).2
  exact tendsto_nhds_unique l1 ((l2.const_mul c).congr fun j => (h _ _ (h3 j).1 (h3 j).2 x).symm)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' R Rf m`. Take `⟨⟨c, hc, pc⟩, -, Φ', ⟨h1, so⟩, hne⟩` from `L.claim m`. Take `⟨Φ, pm⟩` from `(L.matchEx F E σ B _ _ G X om om' R Rf m).2.1 Φ' h1`. Take `⟨x, hx⟩` from `Function.ne_iff.1 hne`. Establish `u : ∀ c', IsConst B G X om om' R Rf c' → c' = c` using `fun c' h => mul_right_cancel₀ hx ((L.polConst_of m h Φ Φ' so pm x).symm.trans (pc Φ Φ' so pm x))`.

Conclude with `⟨⟨Φ', so, hne⟩, ⟨c, L.isConst_of m pc, u⟩, fun c' h => u c' h ▸ hc⟩`.
-/
theorem kConst : KConst := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf m
  obtain ⟨⟨c, hc, pc⟩, -, Φ', ⟨h1, so⟩, hne⟩ := L.claim m
  obtain ⟨Φ, pm⟩ := (L.matchEx F E σ B _ _ G X om om' R Rf m).2.1 Φ' h1
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
  have u : ∀ c', IsConst B G X om om' R Rf c' → c' = c := fun c' h =>
    mul_right_cancel₀ hx ((L.polConst_of m h Φ Φ' so pm x).symm.trans (pc Φ Φ' so pm x))
  exact ⟨⟨Φ', so, hne⟩, ⟨c, L.isConst_of m pc, u⟩, fun c' h => u c' h ▸ hc⟩

/- English proof (translation)
Take `⟨e₁, e₂, s, key⟩` from `L.keyB`. Use `⟨e₁, e₂, s, fun F E _ _ _ _ _ σ B a b G G₁ H H' R R₁ h1 h2 h3 h4 h5 => ?_⟩` and prove the remaining obligations. Take `⟨C, hC, key⟩` from `key F E σ B a b G G₁ H H' ⟨h1, h2, h3, h4, h5⟩ R R₁`. Use `⟨C, hC, fun X om om' Rf om₁ om₁' Rf₁ m m₁ c c₁ hc hc₁ => ?_⟩` and prove the remaining obligations. Take `⟨k1, Φ, hΦ, k2⟩` from `key X om om' Rf om₁ om₁' Rf₁ m m₁ (L.below _)`.

Take `⟨Φ', so, pm⟩` from `(L.matchEx F E σ B _ _ G X om om' R Rf m).1 Φ hΦ`. Take `⟨⟨fa', fb'⟩, sp', -⟩` from `(L.splitEx F E σ B _ _ G X om om' m.triple _ G₁.W H' _ _ h5).2 Φ' ⟨(polMatch_mem pm).2, so⟩`. Establish `e : G.M.I om Φ = c • G.M'.I om' Φ'` using `funext (L.polConst_of m hc Φ Φ' so pm)`. Establish `sp : Split2 G₁.W H' X (G.M.I om Φ) (c • fa') (c • fb')` using `e ▸ split2_smul sp' c`. Take `⟨h₁, l, hl, hne⟩` from `k2 _ _ sp`.

Use `k1 c₁ (L.polConst_of m₁ hc₁) Φ Φ' so pm _ _ _ _ sp sp' h₁ l hl` as an intermediate fact. Establish `f1` using `(L.facNe F E σ B _ _ G X om om' m.triple e₁ e₂ s H.𝔟 H'.𝔟 (-(((a - (b + 2)) / 2 : ℕ) : ℤ))).1`. Establish `hk` using `mul_ne_zero hC f1`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at this hne`. Use `⟨_, inv_mul_cancel₀ hk, ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_inv_mul_iff_mul_eq₀ hk]`. Use `mul_right_cancel₀ (right_ne_zero_of_mul hne) ?_` and prove the remaining obligations. Take the linear combination `this`.
-/
theorem kBeta : KBeta := by
  obtain ⟨e₁, e₂, s, key⟩ := L.keyB
  refine ⟨e₁, e₂, s, fun F E _ _ _ _ _ σ B a b G G₁ H H' R R₁ h1 h2 h3 h4 h5 => ?_⟩
  obtain ⟨C, hC, key⟩ := key F E σ B a b G G₁ H H' ⟨h1, h2, h3, h4, h5⟩ R R₁
  refine ⟨C, hC, fun X om om' Rf om₁ om₁' Rf₁ m m₁ c c₁ hc hc₁ => ?_⟩
  obtain ⟨k1, Φ, hΦ, k2⟩ := key X om om' Rf om₁ om₁' Rf₁ m m₁ (L.below _)
  obtain ⟨Φ', so, pm⟩ := (L.matchEx F E σ B _ _ G X om om' R Rf m).1 Φ hΦ
  obtain ⟨⟨fa', fb'⟩, sp', -⟩ := (L.splitEx F E σ B _ _ G X om om' m.triple _ G₁.W H' _ _ h5).2 Φ' ⟨(polMatch_mem pm).2, so⟩
  have e : G.M.I om Φ = c • G.M'.I om' Φ' := funext (L.polConst_of m hc Φ Φ' so pm)
  have sp : Split2 G₁.W H' X (G.M.I om Φ) (c • fa') (c • fb') := e ▸ split2_smul sp' c
  obtain ⟨h₁, l, hl, hne⟩ := k2 _ _ sp
  have := k1 c₁ (L.polConst_of m₁ hc₁) Φ Φ' so pm _ _ _ _ sp sp' h₁ l hl
  have f1 := (L.facNe F E σ B _ _ G X om om' m.triple e₁ e₂ s H.𝔟 H'.𝔟 (-(((a - (b + 2)) / 2 : ℕ) : ℤ))).1
  have hk := mul_ne_zero hC f1
  simp only [Pi.smul_apply, smul_eq_mul] at this hne
  refine ⟨_, inv_mul_cancel₀ hk, ?_⟩
  rw [eq_inv_mul_iff_mul_eq₀ hk]
  refine mul_right_cancel₀ (right_ne_zero_of_mul hne) ?_
  linear_combination this

/- English proof (translation)
Take `⟨e₁, e₂, s, key⟩` from `L.keyA`. Use `⟨e₁, e₂, s, fun F E _ _ _ _ _ σ B b a' G G₁ H H' R R₁ h1 h2 h3 h4 h5 h6 => ?_⟩` and prove the remaining obligations. Take `⟨C, hC, key⟩` from `key F E σ B b a' G G₁ H H' ⟨h1, h2, h3, h4, h5, h6⟩ R R₁`. Use `⟨C, hC, fun X om om' Rf om₁ om₁' Rf₁ m m₁ c c₁ hc hc₁ => ?_⟩` and prove the remaining obligations. Take `⟨-, Φ, Φ', fa', pm, ⟨sp', rel⟩, h₁, l, hl, hne⟩` from `key X om om' Rf om₁ om₁' Rf₁ m m₁ (L.below _) c₁ (L.polConst_of m₁ hc₁) _ rfl`.

Establish `e : G.M.I om Φ = c • G.M'.I om' Φ'`. Use function extensionality and compare the values at `(L.anAll F E σ B _ _ G X om om' R Rf m h2 c (L.polConst_of m hc) Φ Φ' pm)`. Use `rel _ _ (e ▸ split2_smul sp' c) h₁ l hl` as an intermediate fact. Simplify using `only [Pi.smul_apply, smul_eq_mul] at this`. Conclude with `mul_right_cancel₀ hne this`.
-/
theorem kAlpha : KAlpha := by
  obtain ⟨e₁, e₂, s, key⟩ := L.keyA
  refine ⟨e₁, e₂, s, fun F E _ _ _ _ _ σ B b a' G G₁ H H' R R₁ h1 h2 h3 h4 h5 h6 => ?_⟩
  obtain ⟨C, hC, key⟩ := key F E σ B b a' G G₁ H H' ⟨h1, h2, h3, h4, h5, h6⟩ R R₁
  refine ⟨C, hC, fun X om om' Rf om₁ om₁' Rf₁ m m₁ c c₁ hc hc₁ => ?_⟩
  obtain ⟨-, Φ, Φ', fa', pm, ⟨sp', rel⟩, h₁, l, hl, hne⟩ :=
    key X om om' Rf om₁ om₁' Rf₁ m m₁ (L.below _) c₁ (L.polConst_of m₁ hc₁) _ rfl
  have e : G.M.I om Φ = c • G.M'.I om' Φ' :=
    funext (L.anAll F E σ B _ _ G X om om' R Rf m h2 c (L.polConst_of m hc) Φ Φ' pm)
  have := rel _ _ (e ▸ split2_smul sp' c) h₁ l hl
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hne this

end Leaves

end PositivityTheory.ThKG

end
