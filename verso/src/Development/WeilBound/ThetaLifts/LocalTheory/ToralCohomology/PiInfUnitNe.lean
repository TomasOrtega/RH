import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ParZero
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreLM

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open FockH1Action (Mat Ix fockAct1 fockAct2 cPair)
open Formalism.BasicNotions.TH (upq Jm)
open PositivityTheory.KReal ReciprocityTheory.ChartRestriction.G.ThK.Real

namespace PositivityTheory.ThKG.CayleyTransformDarboux

structure Dic : Prop where
  laws : ActsLaws
  fock : FockEx
  range : PolRange
  fst : LieFirst
  snd : LieSecond
  line : LineEx
  frame : FrameEx
  even_im_hermitian_sub : Parity

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `rcases a with i | i <;> rcases b with j | j <;> simp [Jm, Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply, neg_ite]`.
-/
theorem Jm_eq (r s : ℕ) : Jm r s = Matrix.diagonal (Sum.elim (fun _ => 1) fun _ => -1) := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> simp [Jm, Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply, neg_ite]

/- English proof (translation)
Rewrite using `[Jm_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Apply the tactic sequence `congr 1; funext a; cases a <;> simp`.
-/
theorem Jm_sq (r s : ℕ) : Jm r s * Jm r s = 1 := by
  rw [Jm_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; cases a <;> simp

/- English proof (translation)
Rewrite using `[Jm_eq, Matrix.diagonal_conjTranspose]`. Apply the tactic sequence `congr 1; funext a; cases a <;> simp`.
-/
theorem Jm_star (r s : ℕ) : (Jm r s)ᴴ = Jm r s := by
  rw [Jm_eq, Matrix.diagonal_conjTranspose]
  congr 1; funext a; cases a <;> simp

/- English proof (translation)
Establish `e1 : ∀ Z : Mat r s, Z * Jm r s * Jm r s = Z` using `fun Z => by rw [Matrix.mul_assoc, Jm_sq, Matrix.mul_one]`. Establish `e2 : ∀ Z : Mat r s, Jm r s * (Jm r s * Z) = Z` using `fun Z => by rw [← Matrix.mul_assoc, Jm_sq, Matrix.one_mul]`. Use `⟨(1 / 2 : ℂ) • (Y - Jm r s * Yᴴ * Jm r s), ?_, (-Complex.I / 2) • (Y + Jm r s * Yᴴ * Jm r s), ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Jm_star, Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Jm_sq, Matrix.mul_one, e2]`. Rewrite using `[show star (1 / 2 : ℂ) = 1 / 2 by simp]`.

Use `module`. Simplify using `only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Jm_star, Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Jm_sq, Matrix.mul_one, e2]`. Rewrite using `[show star (-Complex.I / 2 : ℂ) = Complex.I / 2 by simp]`. Use `module`. Rewrite using `[smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I] module`.
-/
theorem upq_split {r s : ℕ} (Y : Mat r s) : ∃ Y₁ ∈ upq r s, ∃ Y₂ ∈ upq r s, Y = Y₁ + Complex.I • Y₂ := by
  have e1 : ∀ Z : Mat r s, Z * Jm r s * Jm r s = Z := fun Z => by rw [Matrix.mul_assoc, Jm_sq, Matrix.mul_one]
  have e2 : ∀ Z : Mat r s, Jm r s * (Jm r s * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, Jm_sq, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (Y - Jm r s * Yᴴ * Jm r s), ?_, (-Complex.I / 2) • (Y + Jm r s * Yᴴ * Jm r s), ?_, ?_⟩
  · simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Jm_star,
      Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_assoc, Jm_sq, Matrix.mul_one, e2]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp]
    module
  · simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Jm_star,
      Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc, Jm_sq, Matrix.mul_one, e2]
    rw [show star (-Complex.I / 2 : ℂ) = Complex.I / 2 by simp]
    module
  · rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I]
    module

/- English proof (translation)
Simplify using `[upq]`.
-/
theorem zero_upq (r s : ℕ) : (0 : Mat r s) ∈ upq r s := by simp [upq]

/- English proof (translation)
Distinguish the cases in `e : i = w`. Substitute `e` using the available equality. Simplify using `using h`. Simplify `zero_upq r s` using `[Pi.single_eq_of_ne e]`.
-/
theorem single_upq {ι : Type} [DecidableEq ι] {r s : ℕ} (w : ι) {Y : Mat r s} (h : Y ∈ upq r s) (i : ι) :
    (Pi.single w Y : ι → Mat r s) i ∈ upq r s := by
  by_cases e : i = w
  · subst e; simpa using h
  · simpa [Pi.single_eq_of_ne e] using zero_upq r s

def sumL {ι P : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup P] [Module ℂ P] {r s : ℕ}
    (aP : ι → Mat r s →ₗ[ℂ] Module.End ℂ P) : (ι → Mat r s) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] _ : ι, P) :=
  ∑ w, (PiTensorProduct.mapMultilinear ℂ (fun _ : ι => P) (fun _ => P)).toLinearMap (fun _ => LinearMap.id) w ∘ₗ aP w ∘ₗ
    LinearMap.proj w

/- English proof (translation)
Rewrite using `[sumL, LinearMap.sum_apply]`. Both sides reduce to the same expression.
-/
theorem sumL_eq {ι P : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup P] [Module ℂ P] {r s : ℕ}
    (aP : ι → Mat r s →ₗ[ℂ] Module.End ℂ P) (Y : ι → Mat r s) :
    sumL aP Y = sumPl (V := fun _ => P) fun i => aP i (Y i) := by
  rw [sumL, LinearMap.sum_apply]; rfl

/- English proof (translation)
Use `choose Y₁ h₁ Y₂ h₂ e using fun w => upq_split (Y w)`. Introduce `x hx`. Rewrite using `[show Y = Y₁ + Complex.I • Y₂ from funext e, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]`. Conclude with `add_mem (h _ h₁ x hx) (N'.smul_mem _ (h _ h₂ x hx))`.
-/
theorem ker_stable {ι V : Type} [AddCommGroup V] [Module ℂ V] {r s : ℕ} (L : (ι → Mat r s) →ₗ[ℂ] Module.End ℂ V)
    (N N' : Submodule ℂ V) (h : ∀ Y, (∀ w, Y w ∈ upq r s) → ∀ x ∈ N, L Y x ∈ N') (Y) : ∀ x ∈ N, L Y x ∈ N' := by
  choose Y₁ h₁ Y₂ h₂ e using fun w => upq_split (Y w)
  intro x hx
  rw [show Y = Y₁ + Complex.I • Y₂ from funext e, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  exact add_mem (h _ h₁ x hx) (N'.smul_mem _ (h _ h₂ x hx))

/- English proof (translation)
Use `choose a ha using fun Y => exists_factor q hq (q ∘ₗ L Y) (h Y)`. Use `⟨⟨⟨a, fun X Y => LinearMap.ext fun m => ?_⟩, fun c X => LinearMap.ext fun m => ?_⟩, ha⟩` and prove the remaining obligations. Take `⟨t, rfl⟩` from `hq m`. Simplify using `[ha]`. Take `⟨t, rfl⟩` from `hq m`.

Simplify using `[ha]`.
-/
theorem exists_act {A V M : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (L : A →ₗ[ℂ] Module.End ℂ V) (q : V →ₗ[ℂ] M) (hq : Function.Surjective q)
    (h : ∀ Y, ∀ x ∈ LinearMap.ker q, L Y x ∈ LinearMap.ker q) :
    ∃ act : A →ₗ[ℂ] Module.End ℂ M, ∀ Y t, act Y (q t) = q (L Y t) := by
  choose a ha using fun Y => exists_factor q hq (q ∘ₗ L Y) (h Y)
  refine ⟨⟨⟨a, fun X Y => LinearMap.ext fun m => ?_⟩, fun c X => LinearMap.ext fun m => ?_⟩, ha⟩
  · obtain ⟨t, rfl⟩ := hq m
    simp [ha]
  · obtain ⟨t, rfl⟩ := hq m
    simp [ha]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM, piInf, compInf, inclR, infEmb_tmul]`.
-/
theorem incM_map {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

/- English proof (translation)
Introduce `e` and use `by have := congrArg (piInf τ) z.mul_inv rw [map_mul, e, zero_mul, map_one] at this exact zero_ne_one this`.
-/
theorem piInf_unit_ne {w : InfinitePlace F} (τ : EmbOver E w) (z : (AE F E)ˣ) : piInf τ (z : AE F E) ≠ 0 := fun e => by
  have := congrArg (piInf τ) z.mul_inv
  rw [map_mul, e, zero_mul, map_one] at this
  exact zero_ne_one this

/- English proof (translation)
Introduce `z hz`. Rewrite using `[MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `h0` using `piInf_unit_ne (τ w) z`. Rewrite using `[zpow_sub₀ (div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0))]`.
-/
theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h0 := piInf_unit_ne (τ w) z
  rw [zpow_sub₀ (div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0))]

/- English proof (translation)
Introduce `r _ x`. Establish `: tens (evI F) (0 : SInf F κ) r = 0` using `by funext y; simp [tens]`. Simplify using `only [this, map_zero, Pi.zero_apply]`. Conclude with `hasDerivAt_const _ _`.
-/
theorem actsD_zero {κ κ' : Type} [Fintype κ] {G : Type} [Monoid G] (om : G →* Module.End ℂ ((κ → AF F) → ℂ)) (g : ℝ → G) :
    ActsD (evI F) (fun t => om (g t)) (0 : SInf F κ) (0 : SInf F κ) := by
  intro r _ x
  have : tens (evI F) (0 : SInf F κ) r = 0 := by funext y; simp [tens]
  simp only [this, map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _

def lamW (B : Base F E) (P Q R S : ℕ) (w : InfinitePlace F) : Ix R S → ℚ
  | .inl k => (if (k : ℕ) < P then ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 - cPair R S else 0) + cPair P Q + (B.mβ w : ℚ) / 2
  | .inr l => (if (l : ℕ) < Q then ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 + cPair R S else 0) - cPair P Q + (B.mβ w : ℚ) / 2

/- English proof (translation)
Establish `par` using `hD.even_im_hermitian_sub F E σ B a a' G X om om' hT`. Take `⟨hb, hg, hc, hw, -⟩` from `hT`. Establish `e1` using `hg.eBig`. Establish `e2` using `hg.aBig`. Take `⟨d2, hd2⟩` from `hg.even`.

Use `choose A hA hAθ using fun w => hD.frame _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)`. Establish `hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w)` using `fun w => by`. Rewrite using `[incM_map, one_smul]`. Conclude with `hA w`. Establish `fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C` using `⟨one_mul _, hA1, hC⟩`.

Take `⟨Φ, hΦ⟩` from `hD.fock F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr`. Establish `hr` using `hD.range F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ`. Establish `hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om` using `hw`. Establish `hW2` using `hD.snd F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1 hc.expβ`. Take `⟨d, hd, hB1⟩` from `hwp.2.1`.

Establish `hW1` using `hD.fst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1 (hasExp_div B.emb hc.expβ hc.expα)`. Establish `mem : ∀ T, Φ T ∈ G.M.Pol B.ψ B.emb` using `fun T => hr ▸ LinearMap.mem_range_self Φ T`. Set `q` to `Rm.p ∘ₗ Φ`. Establish `hq : Function.Surjective q`. Rewrite using `[← LinearMap.range_eq_top, LinearMap.range_comp, hr]`.

Conclude with `hR.quot.onto`. Set `aP` to `fun w : InfinitePlace F => twAct (a - G.p) G.p R S ((B.mβ w : ℂ) / 2)`. Set `a1 : InfinitePlace F → Mat (a - G.p) G.p →ₗ[ℂ] Module.End ℂ (FockH1Action.Pol (a - G.p) G.p R S)` to `fun w => fockAct1 _ _ _ _ + ((((B.mβ w - B.mα w : ℤ) : ℂ) / 2) • Matrix.traceLinearMap _ ℂ ℂ).smulRight 1`. Establish `s2 : ∀ γ ∈ Lines σ G.W, ∀ Y, IsGen B.emb C γ Y → ∀ T, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T) (Φ (sumL aP Y T))` using `fun γ hγ Y hY T => by`. Rewrite using `[sumL_eq]`.

Conclude with `(hD.laws F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW2 γ hγ Y hY T)`. Establish `s1 : ∀ Y T, q (sumL a1 Y T) = 0` using `fun Y T => by`. Use `ker_stable (sumL a1) ⊤ (LinearMap.ker q) (fun Y hY T _ => ?_) Y T trivial` and prove the remaining obligations. Take `⟨γ, hγ, hgen⟩` from `hD.line F E σ _ _ _ B.emb _ 1 A hb.cm hA1 Y hY`. Rewrite using `[sumL_eq]`.

Conclude with `hR.quot.lie γ hγ _ (mem T) _ ((hD.laws F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW1 γ hγ Y hgen T))`. Take `⟨act, ha⟩` from `exists_act (sumL aP) q hq (ker_stable _ _ _ fun Y hY T hT => by`. Take `⟨γ, hγ, hgen⟩` from `hD.line F E σ _ _ _ B.emb _ Complex.I C hb.cm hC Y hY`. Conclude with `(hR.lie γ hγ _ (mem T) 0 (zero_mem _) _ 0 (s2 γ hγ Y hgen T) (actsD_zero (κ' := Unit) om' _) (hT.trans (map_zero _).symm)).trans (map_zero _))`. Establish `side : ∀ w, Side (lamW B (a - G.p) G.p R S w) (ThC (a - G.p) G.p R S ((((B.mα w - B.mβ w : ℤ) : ℚ) / 2 : ℚ) : ℂ)) (thAct _ _ _ _ _ ((B.mβ w : ℂ) / 2))` using `fun w => by`.

Take `⟨k, hk⟩` from `par w`. Establish `hκ` using `hg.kappa w`. Take `⟨n, hn⟩` from `Int.eq_ofNat_of_zero_le (show 0 ≤ k - d2 + S by omega)`. Take `⟨m, hm⟩` from `Int.eq_ofNat_of_zero_le (show 0 ≤ k + d2 - S by omega)`. Establish `hRq : (R : ℚ) + S = d2 + d2` using `by exact_mod_cast (show R + S = d2 + d2 by omega)`.

Establish `hkq : ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 = k` using `by rw [hk]; push_cast; ring`. Establish `hn' : (k : ℚ) - d2 + S = n` using `by exact_mod_cast hn`. Establish `hm' : (k : ℚ) + d2 - S = m` using `by exact_mod_cast hm`. Establish `h1 : ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 = n + cPair R S` using `by rw [hkq, cPair]; linarith`. Establish `h2 : ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 = m - cPair R S` using `by rw [hkq, cPair]; linarith`.

Establish `b1 : (G.p : ℚ) < ((a - G.p : ℕ) : ℚ)` using `by exact_mod_cast (show G.p < a - G.p by omega)`. Establish `b2 : (((a - G.p : ℕ) : ℚ)) < m + G.p` using `by exact_mod_cast (show a - G.p < m + G.p by omega)`. Establish `n0 : 0 < n` using `by omega`. Establish `m0 : 0 < m` using `by omega`. Use `side_of _ ((B.mβ w : ℂ) / 2) _ ((B.mβ w : ℚ) / 2) rfl (by push_cast; rfl) _ (comb_pos (p := a - G.p) (q := G.p) (r := R) (s := S) (by omega) (by omega) n0 m0 _ _ h1 h2 (by rw [cPair]; have : (0 : ℚ) ≤ n := by positivity linarith) (by rw [cPair]; linarith)) (nontrivial_of_pair _ _ …` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `c`. Apply the tactic sequence `rcases c with c | c <;> simp only [lamW, laPos] <;> split_ifs <;> linarith`. Take `⟨f₀, hf₀⟩` from `tens_hw _ _ side aP (fun w => lie_tw _ _ _ _ _) (fun w => thMkC _ _ _ _ _) (fun w => Submodule.mkQ_surjective _) (fun w Y y => (thAct_mk _ _ _ _ _ _ Y y).symm) q hq (fun w y x hx => by`. Establish `hx'` using `(Submodule.Quotient.mk_eq_zero _).1 hx`.

Use `(iSup_le ?_ : _ ≤ LinearMap.ker (q ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap y w)) hx'` and prove the remaining obligations. Introduce and unpack `Z _ ⟨x, rfl⟩`. Use `s1 (Pi.single w Z) (PiTensorProduct.tprod ℂ (Function.update y w x))` as an intermediate fact. Rewrite `this` using `[sumL_eq, sumPl_single, Function.update_idem, Function.update_self]`. Use `Eq.trans ?_ this` and prove the remaining obligations.

Simplify using `only [LinearMap.comp_apply, MultilinearMap.toLinearMap_apply]`. Use `congr 3`. Simplify using `only [a1, act1, chiTr, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, smul_eq_mul, sub_eq_add_neg, ← neg_smul]`. Use `congr 2`. Use `push_cast`.

Use the proof step `ring)`. Use `act (fun Y t => by rw [ha, sumL_eq])`. Use `⟨act, f₀, hf₀, fun γ hγ Y hY f hf => ?_⟩` and prove the remaining obligations. Rewrite `hf` using `[← hr]`. Take `⟨T, rfl⟩` from `hf`.

Conclude with `⟨_, s2 γ hγ Y hY T, (ha Y T).symm⟩`.
-/
theorem exists_mod (hD : Dic) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om om'} {Rm : RealMaps F a a'}
    (hT : IsTriple B G X om om') (hR : IsRealMaps B G om om' Rm) {R S : ℕ} (eR : R + G.p + G.q = a + a') (eS : S = G.p + G.q)
    (C : InfinitePlace F → Matrix (Fin (a + a')) (Ix R S) ℂ)
    (hC : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w)) (hCθ : ∀ w, G.W.θ w * C w = C w * Jm R S) :
    ∃ (act : (InfinitePlace F → Mat R S) →ₗ[ℂ] Module.End ℂ Rm.Pi) (f₀ : Rm.Pi),
      HWMod act (fun w c => (lamW B (a - G.p) G.p R S w c : ℂ)) f₀ ∧
      ∀ γ ∈ Lines σ G.W, ∀ Y, IsGen B.emb C γ Y → ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ : SInf F _,
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ Rm.p f₁ = act Y (Rm.p f) := by
  have par := hD.even_im_hermitian_sub F E σ B a a' G X om om' hT
  obtain ⟨hb, hg, hc, hw, -⟩ := hT
  have e1 := hg.eBig
  have e2 := hg.aBig
  obtain ⟨d2, hd2⟩ := hg.even
  choose A hA hAθ using fun w => hD.frame _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map, one_smul]; exact hA w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC⟩
  obtain ⟨Φ, hΦ⟩ := hD.fock F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hD.range F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hD.snd F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1 hc.expβ
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hD.fst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  have mem : ∀ T, Φ T ∈ G.M.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  let q := Rm.p ∘ₗ Φ
  have hq : Function.Surjective q := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, hr]; exact hR.quot.onto
  let aP := fun w : InfinitePlace F => twAct (a - G.p) G.p R S ((B.mβ w : ℂ) / 2)
  let a1 : InfinitePlace F → Mat (a - G.p) G.p →ₗ[ℂ] Module.End ℂ (FockH1Action.Pol (a - G.p) G.p R S) := fun w =>
    fockAct1 _ _ _ _ + ((((B.mβ w - B.mα w : ℤ) : ℂ) / 2) • Matrix.traceLinearMap _ ℂ ℂ).smulRight 1
  have s2 : ∀ γ ∈ Lines σ G.W, ∀ Y, IsGen B.emb C γ Y → ∀ T,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T) (Φ (sumL aP Y T)) := fun γ hγ Y hY T => by
    rw [sumL_eq]
    exact (hD.laws F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW2 γ hγ Y hY T)
  have s1 : ∀ Y T, q (sumL a1 Y T) = 0 := fun Y T => by
    refine ker_stable (sumL a1) ⊤ (LinearMap.ker q) (fun Y hY T _ => ?_) Y T trivial
    obtain ⟨γ, hγ, hgen⟩ := hD.line F E σ _ _ _ B.emb _ 1 A hb.cm hA1 Y hY
    rw [sumL_eq]
    exact hR.quot.lie γ hγ _ (mem T) _ ((hD.laws F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW1 γ hγ Y hgen T))
  obtain ⟨act, ha⟩ := exists_act (sumL aP) q hq (ker_stable _ _ _ fun Y hY T hT => by
    obtain ⟨γ, hγ, hgen⟩ := hD.line F E σ _ _ _ B.emb _ Complex.I C hb.cm hC Y hY
    exact (hR.lie γ hγ _ (mem T) 0 (zero_mem _) _ 0 (s2 γ hγ Y hgen T) (actsD_zero (κ' := Unit) om' _)
      (hT.trans (map_zero _).symm)).trans (map_zero _))
  have side : ∀ w, Side (lamW B (a - G.p) G.p R S w) (ThC (a - G.p) G.p R S ((((B.mα w - B.mβ w : ℤ) : ℚ) / 2 : ℚ) : ℂ))
      (thAct _ _ _ _ _ ((B.mβ w : ℂ) / 2)) := fun w => by
    obtain ⟨k, hk⟩ := par w
    have hκ := hg.kappa w
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k - d2 + S by omega)
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k + d2 - S by omega)
    have hRq : (R : ℚ) + S = d2 + d2 := by exact_mod_cast (show R + S = d2 + d2 by omega)
    have hkq : ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 = k := by rw [hk]; push_cast; ring
    have hn' : (k : ℚ) - d2 + S = n := by exact_mod_cast hn
    have hm' : (k : ℚ) + d2 - S = m := by exact_mod_cast hm
    have h1 : ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 = n + cPair R S := by rw [hkq, cPair]; linarith
    have h2 : ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 = m - cPair R S := by rw [hkq, cPair]; linarith
    have b1 : (G.p : ℚ) < ((a - G.p : ℕ) : ℚ) := by exact_mod_cast (show G.p < a - G.p by omega)
    have b2 : (((a - G.p : ℕ) : ℚ)) < m + G.p := by exact_mod_cast (show a - G.p < m + G.p by omega)
    have n0 : 0 < n := by omega
    have m0 : 0 < m := by omega
    have := side_of _ ((B.mβ w : ℂ) / 2) _ ((B.mβ w : ℚ) / 2) rfl (by push_cast; rfl) _
      (comb_pos (p := a - G.p) (q := G.p) (r := R) (s := S) (by omega) (by omega) n0 m0 _ _ h1 h2
        (by rw [cPair]; have : (0 : ℚ) ≤ n := by positivity
            linarith) (by rw [cPair]; linarith))
      (nontrivial_of_pair _ _ rfl (pair_pos (by omega) (by omega) n0 m0 _ h1 h2))
    convert this using 1
    funext c
    rcases c with c | c <;> simp only [lamW, laPos] <;> split_ifs <;> linarith
  obtain ⟨f₀, hf₀⟩ := tens_hw _ _ side aP (fun w => lie_tw _ _ _ _ _) (fun w => thMkC _ _ _ _ _)
    (fun w => Submodule.mkQ_surjective _) (fun w Y y => (thAct_mk _ _ _ _ _ _ Y y).symm) q hq
    (fun w y x hx => by
      have hx' := (Submodule.Quotient.mk_eq_zero _).1 hx
      refine (iSup_le ?_ : _ ≤ LinearMap.ker (q ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap y w)) hx'
      rintro Z _ ⟨x, rfl⟩
      have := s1 (Pi.single w Z) (PiTensorProduct.tprod ℂ (Function.update y w x))
      rw [sumL_eq, sumPl_single, Function.update_idem, Function.update_self] at this
      refine Eq.trans ?_ this
      simp only [LinearMap.comp_apply, MultilinearMap.toLinearMap_apply]
      congr 3
      simp only [a1, act1, chiTr, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, smul_eq_mul, sub_eq_add_neg, ← neg_smul]
      congr 2
      push_cast; ring)
    act (fun Y t => by rw [ha, sumL_eq])
  refine ⟨act, f₀, hf₀, fun γ hγ Y hY f hf => ?_⟩
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  exact ⟨_, s2 γ hγ Y hY T, (ha Y T).symm⟩

end PositivityTheory.ThKG.CayleyTransformDarboux

end
