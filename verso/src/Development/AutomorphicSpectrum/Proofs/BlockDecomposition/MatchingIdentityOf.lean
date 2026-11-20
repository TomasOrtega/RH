import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasCompactSupportTj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchId

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Rewrite using `[Subgroup.coe_prod]`. Use `IsOpen.prod ?_ ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.CompanionTheory.IwLevels.KGL_eq_KO]`. Conclude with `GlobalTheory.SplitFlip.isOpen_KO`. Rewrite using `[GlobalTheory.CompanionTheory.IwLevels.KGL_eq_KO]`.

Conclude with `GlobalTheory.SplitFlip.isOpen_KO`.
-/
theorem isOpen_levelSubgroup' (a b : ℕ) (w : Pl E) : IsOpen ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
  rw [Subgroup.coe_prod]
  refine IsOpen.prod ?_ ?_
  · rw [GlobalTheory.CompanionTheory.IwLevels.KGL_eq_KO]
    exact GlobalTheory.SplitFlip.isOpen_KO
  · rw [GlobalTheory.CompanionTheory.IwLevels.KGL_eq_KO]
    exact GlobalTheory.SplitFlip.isOpen_KO

/- English proof (translation)
Take `⟨L₁, L₂, e, h1, h2⟩` from `hd.L a ha w hw`. Rewrite using `[e]`. Use `⟨?_, Subgroup.prod_mono h1.2.1 h2.2.1⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_prod]`. Conclude with `h1.1.prod h2.1`.
-/
theorem L_ok {d : LocData E n} (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hw : w ∈ d.S₀ ∪ d.Bad) :
    IsOpen (d.L a w : Set (GLw a w × GLw (n - a) w)) ∧ d.L a w ≤ K2 a (n - a) w := by
  obtain ⟨L₁, L₂, e, h1, h2⟩ := hd.L a ha w hw
  rw [e]
  refine ⟨?_, Subgroup.prod_mono h1.2.1 h2.2.1⟩
  rw [Subgroup.coe_prod]
  exact h1.1.prod h2.1

/- English proof (translation)
Unfold `LocData.lev`. Use `split_ifs with h1 h2`. Conclude with `⟨GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_open _ _ _, GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_le_maximal _ _ _⟩`. Conclude with `L_ok hd ha h2`. Conclude with `⟨isOpen_levelSubgroup' _ _ _, le_rfl⟩`.
-/
theorem lev_ok {d : LocData E n} (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev a w : Set (GLw a w × GLw (n - a) w)) ∧ d.lev a w ≤ K2 a (n - a) w := by
  unfold LocData.lev
  split_ifs with h1 h2
  · exact ⟨GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_open _ _ _, GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_le_maximal _ _ _⟩
  · exact L_ok hd ha h2
  · exact ⟨isOpen_levelSubgroup' _ _ _, le_rfl⟩

/- English proof (translation)
Unfold `LocData.lev₂`. Use `split_ifs with h2`. Conclude with `L_ok hd ha h2`. Conclude with `⟨isOpen_levelSubgroup' _ _ _, le_rfl⟩`.
-/
theorem lev₂_ok {d : LocData E n} (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev₂ a w : Set (GLw a w × GLw (n - a) w)) ∧ d.lev₂ a w ≤ K2 a (n - a) w := by
  unfold LocData.lev₂
  split_ifs with h2
  · exact L_ok hd ha h2
  · exact ⟨isOpen_levelSubgroup' _ _ _, le_rfl⟩

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `[mconv, hint]`.
-/
theorem mconv_zero_right {a b : ℕ} {w : Pl E} (u : LF a b w) : mconv u (fun _ => 0) = (0 : LF a b w) := by
  funext m
  simp [mconv, hint]

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `[mconv, hint]`.
-/
theorem mconv_zero_left {a b : ℕ} {w : Pl E} (u : LF a b w) : mconv (fun _ => 0) u = (0 : LF a b w) := by
  funext m
  simp [mconv, hint]

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single y]`. Simplify using `[LocData.diag]`. Introduce `z _ hz`. Establish `: d.diag g z y = fun _ => 0`. Simplify using `only [LocData.diag, if_neg hz]`.

Both sides reduce to the same expression. Rewrite using `[this, mconv_zero_right]`. Simplify using the standard rewrite rules.
-/
theorem sum_mconv_diag_right (d : LocData E n) {a : ℕ} {w : Pl E} (F : d.kap w → LF a (n - a) w)
    (g : d.kap w → LF a (n - a) w) (y : d.kap w) :
    ∑ z, mconv (F z) (d.diag g z y) = mconv (F y) (g y) := by
  rw [Finset.sum_eq_single y]
  · simp [LocData.diag]
  · intro z _ hz
    have : d.diag g z y = fun _ => 0 := by
      simp only [LocData.diag, if_neg hz]
      rfl
    rw [this, mconv_zero_right]
  · simp

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single x]`. Simplify using `[LocData.diag]`. Introduce `z _ hz`. Establish `: d.diag g x z = fun _ => 0`. Simplify using `only [LocData.diag, if_neg (Ne.symm hz)]`.

Both sides reduce to the same expression. Rewrite using `[this, mconv_zero_left]`. Simplify using the standard rewrite rules.
-/
theorem sum_mconv_diag_left (d : LocData E n) {a : ℕ} {w : Pl E} (F : d.kap w → LF a (n - a) w)
    (g : d.kap w → LF a (n - a) w) (x : d.kap w) :
    ∑ z, mconv (d.diag g x z) (F z) = mconv (g x) (F x) := by
  rw [Finset.sum_eq_single x]
  · simp [LocData.diag]
  · intro z _ hz
    have : d.diag g x z = fun _ => 0 := by
      simp only [LocData.diag, if_neg (Ne.symm hz)]
      rfl
    rw [this, mconv_zero_left]
  · simp

/- English proof (translation)
Establish `I1 : ∀ w f, IsHecke (d.lev a w) f → mconv (idem (d.lev a w)) f = f ∧ mconv f (idem (d.lev a w)) = f` using `fun w f hf => by`. Take `⟨o, l⟩` from `lev_ok hd ha w`. Take `⟨h1, h2⟩` from `(hI E a (n - a) w _ o l).2.2 f hf |>.imp id (fun h => h.1)`. Conclude with `⟨h1, h2⟩`. Establish `I2' : ∀ w f, IsHecke (d.lev₂ a w) f → mconv (idem (d.lev₂ a w)) f = f ∧ mconv f (idem (d.lev₂ a w)) = f` using `fun w f hf => by`.

Take `⟨o, l⟩` from `lev₂_ok hd ha w`. Take `⟨h1, h2⟩` from `(hI E a (n - a) w _ o l).2.2 f hf |>.imp id (fun h => h.1)`. Conclude with `⟨h1, h2⟩`. Use `⟨⟨fun w hw => ?_, fun w hw => ?_, ?_⟩, ⟨fun w hw => ?_, fun w hw => ?_, ?_⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x y`.

Conclude with `(sum_mconv_diag_right d (L.m w x) (fun _ => idem (d.lev a w)) y).trans (I1 w _ (hm w hw x y)).2`. Conclude with `(I1 w _ (hs w hw)).2`. Use function extensionality and compare the values at `w`. Conclude with `(I2' w _ (ht w)).2`. Use function extensionality and compare the values at `x y`.

Conclude with `(sum_mconv_diag_left d (fun z => L.m w z y) (fun _ => idem (d.lev a w)) x).trans (I1 w _ (hm w hw x y)).1`. Conclude with `(I1 w _ (hs w hw)).1`. Use function extensionality and compare the values at `w`. Conclude with `(I2' w _ (ht w)).1`.
-/
theorem eqv_of_hecke (hI : IdemAlg) {d : LocData E n} (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (L : LM d.kap a (n - a))
    (hm : ∀ w ∈ d.P, ∀ x y, IsHecke (d.lev a w) (L.m w x y))
    (hs : ∀ w, w ∉ d.P → IsHecke (d.lev a w) (L.s w))
    (ht : ∀ w, IsHecke (d.lev₂ a w) (L.t w)) :
    (L.mul (d.eL a)).Eqv d.P L ∧ ((d.eL a).mul L).Eqv d.P L := by
  have I1 : ∀ w f, IsHecke (d.lev a w) f → mconv (idem (d.lev a w)) f = f ∧ mconv f (idem (d.lev a w)) = f :=
    fun w f hf => by
      obtain ⟨o, l⟩ := lev_ok hd ha w
      obtain ⟨h1, h2⟩ := (hI E a (n - a) w _ o l).2.2 f hf |>.imp id (fun h => h.1)
      exact ⟨h1, h2⟩
  have I2' : ∀ w f, IsHecke (d.lev₂ a w) f → mconv (idem (d.lev₂ a w)) f = f ∧ mconv f (idem (d.lev₂ a w)) = f :=
    fun w f hf => by
      obtain ⟨o, l⟩ := lev₂_ok hd ha w
      obtain ⟨h1, h2⟩ := (hI E a (n - a) w _ o l).2.2 f hf |>.imp id (fun h => h.1)
      exact ⟨h1, h2⟩
  refine ⟨⟨fun w hw => ?_, fun w hw => ?_, ?_⟩, ⟨fun w hw => ?_, fun w hw => ?_, ?_⟩⟩
  · funext x y
    exact (sum_mconv_diag_right d (L.m w x) (fun _ => idem (d.lev a w)) y).trans (I1 w _ (hm w hw x y)).2
  · exact (I1 w _ (hs w hw)).2
  · funext w
    exact (I2' w _ (ht w)).2
  · funext x y
    exact (sum_mconv_diag_left d (fun z => L.m w z y) (fun _ => idem (d.lev a w)) x).trans (I1 w _ (hm w hw x y)).1
  · exact (I1 w _ (hs w hw)).1
  · funext w
    exact (I2' w _ (ht w)).1

section Hecke

variable {G : Type} [Group G] [TopologicalSpace G]

/- English proof (translation)
Assemble the required witnesses or components as `⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩`.
-/
theorem isHecke_zero' (L : Subgroup G) : IsHecke L (fun _ : G => (0 : ℂ)) :=
  ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨HasCompactSupport.mono h.1 (Function.support_const_smul_subset c f), fun k hk x => by simp only [Pi.smul_apply, (h.2 k hk x).1, (h.2 k hk x).2, and_self]⟩`.
-/
theorem isHecke_smul' {L : Subgroup G} {f : G → ℂ} (c : ℂ) (h : IsHecke L f) : IsHecke L (c • f) :=
  ⟨HasCompactSupport.mono h.1 (Function.support_const_smul_subset c f), fun k hk x => by
    simp only [Pi.smul_apply, (h.2 k hk x).1, (h.2 k hk x).2, and_self]⟩

end Hecke

/- English proof (translation)
Unfold `LocData.diag`. Use `split_ifs`. Conclude with `hf x`. Conclude with `isHecke_zero' L`.
-/
theorem isHecke_diag (d : LocData E n) {a : ℕ} {w : Pl E} {L : Subgroup (GLw a w × GLw (n - a) w)}
    {f : d.kap w → LF a (n - a) w} (hf : ∀ x, IsHecke L (f x)) (x y : d.kap w) : IsHecke L (d.diag f x y) := by
  unfold LocData.diag
  split_ifs
  · exact hf x
  · exact isHecke_zero' L

/- English proof (translation)
The claim follows from `(hI E a (n - a) w _ (lev_ok hd ha w).1 (lev_ok hd ha w).2).1`.
-/
theorem idem_lev (hI : IdemAlg) {d : LocData E n} (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) :
    IsHecke (d.lev a w) (idem (d.lev a w)) :=
  (hI E a (n - a) w _ (lev_ok hd ha w).1 (lev_ok hd ha w).2).1

/- English proof (translation)
The claim follows from `(hI E a (n - a) w _ (lev₂_ok hd ha w).1 (lev₂_ok hd ha w).2).1`.
-/
theorem idem_lev₂ (hI : IdemAlg) {d : LocData E n} (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) :
    IsHecke (d.lev₂ a w) (idem (d.lev₂ a w)) :=
  (hI E a (n - a) w _ (lev₂_ok hd ha w).1 (lev₂_ok hd ha w).2).1

/- English proof (translation)
Set `X : ∀ v : P, κ v` to `Function.update (fun v => (hne v).some) ⟨w, hw⟩ x`. Set `Y : ∀ v : P, κ v` to `Function.update (fun v => (hne v).some) ⟨w, hw⟩ y`. Take `⟨K₁, K₂, -, -, hT⟩` from `h.1 X Y`. Use `(hT.1 w).1` as an intermediate fact. Simplify `this` using `[LM.ent, hw, X, Y]`.
-/
theorem compact_m {κ : Pl E → Type} [∀ w, Fintype (κ w)] {a b : ℕ} {P : Finset (Pl E)} {L : LM κ a b}
    (hne : ∀ w, Nonempty (κ w)) (h : L.Ok P) {w : Pl E} (hw : w ∈ P) (x y : κ w) : HasCompactSupport (L.m w x y) := by
  let X : ∀ v : P, κ v := Function.update (fun v => (hne v).some) ⟨w, hw⟩ x
  let Y : ∀ v : P, κ v := Function.update (fun v => (hne v).some) ⟨w, hw⟩ y
  obtain ⟨K₁, K₂, -, -, hT⟩ := h.1 X Y
  have := (hT.1 w).1
  simpa [LM.ent, hw, X, Y] using this

/- English proof (translation)
Take `⟨h1, h2⟩` from `Subgroup.mem_prod.1 hk`. Unfold `LocData.qT`. Distinguish the cases in `h : LocData.admitted n a s`. Simplify using `only [dif_pos h, dc2, Prod.fst_mul, Prod.snd_mul, GlobalTheory.CompanionTheory.MatchPow.dcos_left' _ h1, GlobalTheory.CompanionTheory.MatchPow.dcos_left' _ h2, GlobalTheory.CompanionTheory.MatchPow.dcos_right' _ h1, GlobalTheory.CompanionTheory.MatchPow.dcos_right' _ h2, and_self …`. Simplify using `only [dif_neg h, and_self]`.
-/
theorem qT_inv (d : LocData E n) {a : ℕ} {w : Pl E} (s : Finset (Fin (n / 2))) {k : GLw a w × GLw (n - a) w}
    (hk : k ∈ I2 a (n - a) w) (y : GLw a w × GLw (n - a) w) :
    d.qT a w s (k * y) = d.qT a w s y ∧ d.qT a w s (y * k) = d.qT a w s y := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hk
  unfold LocData.qT
  by_cases h : LocData.admitted n a s
  · simp only [dif_pos h, dc2, Prod.fst_mul, Prod.snd_mul, GlobalTheory.CompanionTheory.MatchPow.dcos_left' _ h1,
      GlobalTheory.CompanionTheory.MatchPow.dcos_left' _ h2, GlobalTheory.CompanionTheory.MatchPow.dcos_right' _ h1, GlobalTheory.CompanionTheory.MatchPow.dcos_right' _ h2, and_self]
  · simp only [dif_neg h, and_self]

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.CtHecke.cMu`. Establish `e : ((-1) ^ (a * b) * GeneralLinearGroup.det (κ * m).1 ^ b * GeneralLinearGroup.det (κ * m).2 ^ a : (w.adicCompletion E)ˣ) = ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) * (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a)`. Simplify using `only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]`. The two sides agree by associativity and commutativity. Rewrite using `[e, map_mul, h1, mul_one]`.
-/
theorem cMu_left {a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ} {κ : GLw a w × GLw b w}
    (h1 : μ (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) = 1) (m : GLw a w × GLw b w) :
    GlobalTheory.CompanionTheory.CtHecke.cMu μ (κ * m) = GlobalTheory.CompanionTheory.CtHecke.cMu μ m := by
  unfold GlobalTheory.CompanionTheory.CtHecke.cMu
  have e : ((-1) ^ (a * b) * GeneralLinearGroup.det (κ * m).1 ^ b * GeneralLinearGroup.det (κ * m).2 ^ a :
      (w.adicCompletion E)ˣ) = ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) *
        (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
    ac_rfl
  rw [e, map_mul, h1, mul_one]

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.CtHecke.cMu`. Establish `e : ((-1) ^ (a * b) * GeneralLinearGroup.det (m * κ).1 ^ b * GeneralLinearGroup.det (m * κ).2 ^ a : (w.adicCompletion E)ˣ) = ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) * (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a)`. Simplify using `only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]`. The two sides agree by associativity and commutativity. Rewrite using `[e, map_mul, h1, mul_one]`.
-/
theorem cMu_right {a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ} {κ : GLw a w × GLw b w}
    (h1 : μ (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) = 1) (m : GLw a w × GLw b w) :
    GlobalTheory.CompanionTheory.CtHecke.cMu μ (m * κ) = GlobalTheory.CompanionTheory.CtHecke.cMu μ m := by
  unfold GlobalTheory.CompanionTheory.CtHecke.cMu
  have e : ((-1) ^ (a * b) * GeneralLinearGroup.det (m * κ).1 ^ b * GeneralLinearGroup.det (m * κ).2 ^ a :
      (w.adicCompletion E)ˣ) = ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) *
        (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
    ac_rfl
  rw [e, map_mul, h1, mul_one]

/- English proof (translation)
Take `⟨ho, hle, hN, hX, hun, hf⟩` from `hd.K' w hS`. Take `⟨-, hc, hb⟩` from `GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_locally_constant E n a (n - a) (Nat.add_sub_of_le ha) w (d.K' w) ho hle hN (d.X w) hX hun (d.e w) hf x hx y hy`. Establish `e : d.mac a ha w (d.e w) x y = ((d.sgn a w * ((d.X w).card : ℂ))⁻¹) • fun m => GlobalTheory.CompanionTheory.CtHecke.cMu (d.μ w) m * phi3 (Nat.add_sub_of_le ha) w (d.e w) x y m` using `rfl`. Rewrite using `[e]`. Use `isHecke_smul' _ ⟨hc.mul_left, fun k hk m => ?_⟩` and prove the remaining obligations.

Take `⟨l1, l2⟩` from `hd.LS a ha w hS k hk`. Take `⟨l3, -⟩` from `hd.LS a ha w hS 1 (one_mem _)`. Establish `r1` using `hb k l1 1 l3 m`. Establish `r2` using `hb 1 l3 k l1 m`. Rewrite `r1` using `[mul_one]`.

Rewrite `r2` using `[one_mul]`. Conclude with `⟨by simp only [cMu_left l2, r1], by simp only [cMu_right l2, r2]⟩`.
-/
theorem mac_hecke {d : LocData E n} (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hS : w ∈ d.S₀)
    {x y : GLw n w} (hx : x ∈ d.X w) (hy : y ∈ d.X w) : IsHecke (d.L a w) (d.mac a ha w (d.e w) x y) := by
  obtain ⟨ho, hle, hN, hX, hun, hf⟩ := hd.K' w hS
  obtain ⟨-, hc, hb⟩ := GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_locally_constant E n a (n - a) (Nat.add_sub_of_le ha) w (d.K' w) ho hle hN (d.X w) hX hun
    (d.e w) hf x hx y hy
  have e : d.mac a ha w (d.e w) x y = ((d.sgn a w * ((d.X w).card : ℂ))⁻¹) • fun m =>
      GlobalTheory.CompanionTheory.CtHecke.cMu (d.μ w) m * phi3 (Nat.add_sub_of_le ha) w (d.e w) x y m := rfl
  rw [e]
  refine isHecke_smul' _ ⟨hc.mul_left, fun k hk m => ?_⟩
  obtain ⟨l1, l2⟩ := hd.LS a ha w hS k hk
  obtain ⟨l3, -⟩ := hd.LS a ha w hS 1 (one_mem _)
  have r1 := hb k l1 1 l3 m
  have r2 := hb 1 l3 k l1 m
  rw [mul_one] at r1
  rw [one_mul] at r2
  exact ⟨by simp only [cMu_left l2, r1], by simp only [cMu_right l2, r2]⟩

/- English proof (translation)
The claim follows from `isHecke_smul' _ (GlobalTheory.CompanionTheory.CtHecke.isHecke_ctT E n a (n - a) (Nat.add_sub_of_le ha) w (d.μ w) (d.ϖ w) hG.1 (hd.unif w) hG.2.2.2.2 k)`.
-/
theorem hc_hecke {d : LocData E n} (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hG : d.Good w) (k : ℕ) :
    IsHecke (K2 a (n - a) w) (d.hc a ha w k) :=
  isHecke_smul' _ (GlobalTheory.CompanionTheory.CtHecke.isHecke_ctT E n a (n - a) (Nat.add_sub_of_le ha) w (d.μ w) (d.ϖ w) hG.1 (hd.unif w)
    hG.2.2.2.2 k)

/- English proof (translation)
Establish `: w ∉ d.S₀ ∪ d.Bad` using `by simp [hG.2.2.1, hG.2.2.2.1]`. Simplify using `only [LocData.lev, if_neg hG.2.1, if_neg this]`.
-/
theorem lev_good {d : LocData E n} {a : ℕ} {w : Pl E} (hG : d.Good w) : d.lev a w = K2 a (n - a) w := by
  have : w ∉ d.S₀ ∪ d.Bad := by simp [hG.2.2.1, hG.2.2.2.1]
  simp only [LocData.lev, if_neg hG.2.1, if_neg this]

/- English proof (translation)
Establish `: w ∉ d.S₀ ∪ d.Bad` using `by simp [hG.2.2.1, hG.2.2.2.1]`. Simplify using `only [LocData.lev₂, if_neg this]`.
-/
theorem lev₂_good {d : LocData E n} {a : ℕ} {w : Pl E} (hG : d.Good w) : d.lev₂ a w = K2 a (n - a) w := by
  have : w ∉ d.S₀ ∪ d.Bad := by simp [hG.2.2.1, hG.2.2.2.1]
  simp only [LocData.lev₂, if_neg this]

/- English proof (translation)
The claim follows from `eqv_of_hecke hI hd ha _ (fun w _ x y => isHecke_diag d (fun _ => idem_lev hI hd ha w) x y) (fun w _ => idem_lev hI hd ha w) (fun w => idem_lev₂ hI hd ha w)`.
-/
theorem eqv_eL (hI : IdemAlg) {d : LocData E n} (hd : d.Ok) {a : ℕ} (ha : a ≤ n) :
    ((d.eL a).mul (d.eL a)).Eqv d.P (d.eL a) ∧ ((d.eL a).mul (d.eL a)).Eqv d.P (d.eL a) :=
  eqv_of_hecke hI hd ha _ (fun w _ x y => isHecke_diag d (fun _ => idem_lev hI hd ha w) x y)
    (fun w _ => idem_lev hI hd ha w) (fun w => idem_lev₂ hI hd ha w)

/- English proof (translation)
Establish `hm : ∀ w x y, IsHecke (d.lev a w) ((d.fixL a).m w x y)` using `fun w x y => by show IsHecke _ (d.diag (fun _ => if w ∈ d.T then idem (d.lev a w) else d.sgn a w • idem (d.lev a w)) x y)`. Use `isHecke_diag d (fun _ => ?_) x y` and prove the remaining obligations. Use `split_ifs`. Conclude with `idem_lev hI hd ha w`. Conclude with `isHecke_smul' _ (idem_lev hI hd ha w)`.

Use `eqv_of_hecke hI hd ha _ (fun w _ x y => hm w x y) (fun w hw => ?_) (fun w => idem_lev₂ hI hd ha w)` and prove the remaining obligations. Use `show IsHecke _ (if w ∈ d.Bad then d.fix a w else idem (d.lev a w)) split_ifs with hB`. Establish `hT : w ∉ d.T` using `fun h => hw (Finset.mem_union_left _ h)`. Establish `e : d.lev a w = d.L a w`. Simplify using `only [LocData.lev, if_neg hT, if_pos (Finset.mem_union_right _ hB)]`.

Rewrite using `[e]`. Conclude with `hd.fix a ha w hB`. Conclude with `idem_lev hI hd ha w`.
-/
theorem eqv_fixL (hI : IdemAlg) {d : LocData E n} (hd : d.Ok) {a : ℕ} (ha : a ≤ n) :
    ((d.fixL a).mul (d.eL a)).Eqv d.P (d.fixL a) ∧ ((d.eL a).mul (d.fixL a)).Eqv d.P (d.fixL a) := by
  have hm : ∀ w x y, IsHecke (d.lev a w) ((d.fixL a).m w x y) := fun w x y => by
    show IsHecke _ (d.diag (fun _ => if w ∈ d.T then idem (d.lev a w) else d.sgn a w • idem (d.lev a w)) x y)
    refine isHecke_diag d (fun _ => ?_) x y
    split_ifs
    · exact idem_lev hI hd ha w
    · exact isHecke_smul' _ (idem_lev hI hd ha w)
  refine eqv_of_hecke hI hd ha _ (fun w _ x y => hm w x y) (fun w hw => ?_) (fun w => idem_lev₂ hI hd ha w)
  · show IsHecke _ (if w ∈ d.Bad then d.fix a w else idem (d.lev a w))
    split_ifs with hB
    · have hT : w ∉ d.T := fun h => hw (Finset.mem_union_left _ h)
      have e : d.lev a w = d.L a w := by
        simp only [LocData.lev, if_neg hT, if_pos (Finset.mem_union_right _ hB)]
      rw [e]
      exact hd.fix a ha w hB
    · exact idem_lev hI hd ha w

/- English proof (translation)
Take `⟨h1, h2⟩` from `hne d hd a ha`. Use `eqv_of_hecke hI hd ha _ (fun w hw x y => ?_) (fun w _ => idem_lev hI hd ha w) (fun w => idem_lev₂ hI hd ha w)` and prove the remaining obligations. Distinguish the cases in `hT : w ∈ d.T`. Establish `e : d.lev a w = I2 a (n - a) w` using `by simp only [LocData.lev, if_pos hT]`. Rewrite using `[e]`.

Use `⟨compact_m h1 h2 hw x y, fun k hk m => ?_⟩` and prove the remaining obligations. Use `show (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else _) (k * m) = (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else _) m ∧ (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else _) (m * k) = (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else _) m`. Simplify using `only [if_pos hT, LocData.diag]`. Use `split_ifs`. Conclude with `qT_inv d _ hk m`.

Conclude with `⟨rfl, rfl⟩`. Establish `hS : w ∈ d.S₀` using `(Finset.mem_union.1 hw).resolve_left hT`. Establish `e : d.lev a w = d.L a w`. Simplify using `only [LocData.lev, if_neg hT, if_pos (Finset.mem_union_left _ hS)]`. Establish `mem : ∀ x : d.kap w, x.1.2 ∈ d.X w` using `fun x => by`.

Use `x.2` as an intermediate fact. Simplify using `only [LocData.idx, if_neg hT, if_pos hS] at this`. Conclude with `(Finset.mem_product.1 this).2`. Rewrite using `[e]`. Use `show IsHecke _ (if w ∈ d.T then _ else d.mac a ha w (d.e w) x.1.2 y.1.2)`.

Rewrite using `[if_neg hT]`. Conclude with `mac_hecke hd ha hS (mem x) (mem y)`.
-/
theorem eqv_betaL (hI : IdemAlg) (hne : ∀ (d : LocData E n) (_ : d.Ok) (a : ℕ) (ha : a ≤ n),
      (∀ w, Nonempty (d.kap w)) ∧ (d.betaL a ha).Ok d.P) {d : LocData E n} (hd : d.Ok) {a : ℕ} (ha : a ≤ n) :
    ((d.betaL a ha).mul (d.eL a)).Eqv d.P (d.betaL a ha) ∧ ((d.eL a).mul (d.betaL a ha)).Eqv d.P (d.betaL a ha) := by
  obtain ⟨h1, h2⟩ := hne d hd a ha
  refine eqv_of_hecke hI hd ha _ (fun w hw x y => ?_) (fun w _ => idem_lev hI hd ha w) (fun w => idem_lev₂ hI hd ha w)
  by_cases hT : w ∈ d.T
  · have e : d.lev a w = I2 a (n - a) w := by simp only [LocData.lev, if_pos hT]
    rw [e]
    refine ⟨compact_m h1 h2 hw x y, fun k hk m => ?_⟩
    show (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else _) (k * m) = (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else _) m ∧
      (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else _) (m * k) = (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else _) m
    simp only [if_pos hT, LocData.diag]
    split_ifs
    · exact qT_inv d _ hk m
    · exact ⟨rfl, rfl⟩
  · have hS : w ∈ d.S₀ := (Finset.mem_union.1 hw).resolve_left hT
    have e : d.lev a w = d.L a w := by
      simp only [LocData.lev, if_neg hT, if_pos (Finset.mem_union_left _ hS)]
    have mem : ∀ x : d.kap w, x.1.2 ∈ d.X w := fun x => by
      have := x.2
      simp only [LocData.idx, if_neg hT, if_pos hS] at this
      exact (Finset.mem_product.1 this).2
    rw [e]
    show IsHecke _ (if w ∈ d.T then _ else d.mac a ha w (d.e w) x.1.2 y.1.2)
    rw [if_neg hT]
    exact mac_hecke hd ha hS (mem x) (mem y)

/- English proof (translation)
Use `eqv_of_hecke hI hd ha _ (fun v _ x y => isHecke_diag d (fun _ => idem_lev hI hd ha v) x y) (fun v _ => ?_) (fun v => ?_)` and prove the remaining obligations. Consider the cases of `intersection_update_fsHerm_neg_one`. Distinguish the cases in `e : v = w`. Substitute `e` using the available equality. Simplify using `only [LocData.hL, Bool.false_eq_true, if_false, Function.update_self]`.

Rewrite using `[lev_good hG]`. Conclude with `hc_hecke hd ha hG k`. Simplify using `only [LocData.hL, Bool.false_eq_true, if_false, Function.update_of_ne e]`. Conclude with `idem_lev hI hd ha v`. Simplify using `only [LocData.hL, if_true]`.

Conclude with `idem_lev hI hd ha v`. Consider the cases of `intersection_update_fsHerm_neg_one`. Simplify using `only [LocData.hL, Bool.false_eq_true, if_false]`. Conclude with `idem_lev₂ hI hd ha v`. Distinguish the cases in `e : v = w`.

Substitute `e` using the available equality. Simplify using `only [LocData.hL, if_true, Function.update_self]`. Rewrite using `[lev₂_good hG]`. Conclude with `hc_hecke hd ha hG k`. Simplify using `only [LocData.hL, if_true, Function.update_of_ne e]`.

Conclude with `idem_lev₂ hI hd ha v`.
-/
theorem eqv_hL (hI : IdemAlg) {d : LocData E n} (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hG : d.Good w) (k : ℕ)
    (intersection_update_fsHerm_neg_one : Bool) :
    ((d.hL a ha w k intersection_update_fsHerm_neg_one).mul (d.eL a)).Eqv d.P (d.hL a ha w k intersection_update_fsHerm_neg_one) ∧
      ((d.eL a).mul (d.hL a ha w k intersection_update_fsHerm_neg_one)).Eqv d.P (d.hL a ha w k intersection_update_fsHerm_neg_one) := by
  refine eqv_of_hecke hI hd ha _ (fun v _ x y => isHecke_diag d (fun _ => idem_lev hI hd ha v) x y) (fun v _ => ?_)
    (fun v => ?_)
  · cases intersection_update_fsHerm_neg_one
    · by_cases e : v = w
      · subst e
        simp only [LocData.hL, Bool.false_eq_true, if_false, Function.update_self]
        rw [lev_good hG]
        exact hc_hecke hd ha hG k
      · simp only [LocData.hL, Bool.false_eq_true, if_false, Function.update_of_ne e]
        exact idem_lev hI hd ha v
    · simp only [LocData.hL, if_true]
      exact idem_lev hI hd ha v
  · cases intersection_update_fsHerm_neg_one
    · simp only [LocData.hL, Bool.false_eq_true, if_false]
      exact idem_lev₂ hI hd ha v
    · by_cases e : v = w
      · subst e
        simp only [LocData.hL, if_true, Function.update_self]
        rw [lev₂_good hG]
        exact hc_hecke hd ha hG k
      · simp only [LocData.hL, if_true, Function.update_of_ne e]
        exact idem_lev₂ hI hd ha v

/- English proof (translation)
Introduce `hI hLoc E _ _ _ n d hd a ha L hL`. Break down `hL with rfl | rfl | rfl | ⟨w, k, intersection_update_fsHerm_neg_one, hG, rfl⟩` into its components or cases. Conclude with `eqv_betaL hI (fun d hd a ha => ⟨(hLoc E n d hd a ha).1, (hLoc E n d hd a ha).2.1⟩) hd ha`. Conclude with `eqv_fixL hI hd ha`. Conclude with `eqv_eL hI hd ha`.

Conclude with `eqv_hL hI hd ha hG k intersection_update_fsHerm_neg_one`.
-/
theorem matchLMIdOf : PositivityTheory.Rg.BcB.F.MLM.MatchLMIdOf := by
  intro hI hLoc E _ _ _ n d hd a ha L hL
  rcases hL with rfl | rfl | rfl | ⟨w, k, intersection_update_fsHerm_neg_one, hG, rfl⟩
  · exact eqv_betaL hI (fun d hd a ha => ⟨(hLoc E n d hd a ha).1, (hLoc E n d hd a ha).2.1⟩) hd ha
  · exact eqv_fixL hI hd ha
  · exact eqv_eL hI hd ha
  · exact eqv_hL hI hd ha hG k intersection_update_fsHerm_neg_one

end GlobalTheory.CompanionTheory.MatchId

end
