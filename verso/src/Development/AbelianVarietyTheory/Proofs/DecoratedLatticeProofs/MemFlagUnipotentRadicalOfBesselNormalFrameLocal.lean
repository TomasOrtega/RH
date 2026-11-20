import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

namespace GlobalTheory.LocFlag

/- English proof (translation)
Establish `hAB : (P * β) * (γ * J) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc β, hβγ, Matrix.one_mul, hPJ]`. Establish `hBA : (γ * J) * (P * β) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc J, hJP, Matrix.one_mul, hγβ]`. Establish `hB : ∀ t b, lw t ≠ lv b → (γ ⬝ J) t b = 0`.

Introduce `t b h`. Generalize the expression as in `P * β = A at hA hAB hBA`. Generalize the expression as in `γ * J = B at hAB hBA`. Establish `h1 : diagonal (fun a => if lv a = lv b then (1 : k) else 0) * A = A * diagonal (fun r => if lw r = lv b then (1 : k) else 0)`. Use extensionality with `a r`.

Rewrite using `[diagonal_mul, mul_diagonal]`. Distinguish the cases in `e : lv a = lw r`. Rewrite using `[e, mul_comm]`. Rewrite using `[hA a r e, mul_zero, zero_mul]`. Establish `h2 : B * diagonal (fun a => if lv a = lv b then (1 : k) else 0) = diagonal (fun r => if lw r = lv b then (1 : k) else 0) * B`.

Rewrite using `[← Matrix.mul_one (B * _), ← hAB, ← Matrix.mul_assoc, Matrix.mul_assoc B, h1, ← Matrix.mul_assoc, hBA, Matrix.one_mul]`. Establish `h3` using `congrFun (congrFun h2 t) b`. Rewrite `h3` using `[diagonal_mul, mul_diagonal, if_pos rfl, if_neg h, mul_one, zero_mul]`. Then use the resulting hypothesis. Establish `e : P * (β * q * γ - 1) * J = (P * β) * (q - 1) * (γ * J)`. Rewrite using `[← hβγ]`.

Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul]`. Rewrite using `[e, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations. Distinguish the cases in `ht : lw t = lv b`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]`.

Introduce `r _`. Distinguish the cases in `hr : lv a = lw r`. Rewrite using `[Matrix.sub_apply, hq r t (by omega), sub_self, mul_zero]`. Rewrite using `[hA a r hr, zero_mul]`. Rewrite using `[hB t b ht, mul_zero]`.
-/
theorem conj_vanish {k : Type} [CommRing k] {Z Y M : Type} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
    [Fintype M] [DecidableEq M] (lv : Z → ℕ) (lw : Y → ℕ) (P : Matrix Z M k) (J : Matrix M Z k) (β : Matrix M Y k)
    (γ : Matrix Y M k) (hPJ : P * J = 1) (hJP : J * P = 1) (hβγ : β * γ = 1) (hγβ : γ * β = 1)
    (hA : ∀ a r, lv a ≠ lw r → (P ⬝ β) a r = 0) (q : Matrix Y Y k)
    (hq : ∀ r s, lw s ≤ lw r → q r s = (1 : Matrix Y Y k) r s) (a b : Z) (hab : lv b ≤ lv a) :
    (P ⬝ (β * q * γ - 1) ⬝ J) a b = 0 := by
  have hAB : (P * β) * (γ * J) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc β, hβγ, Matrix.one_mul, hPJ]
  have hBA : (γ * J) * (P * β) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J, hJP, Matrix.one_mul, hγβ]
  have hB : ∀ t b, lw t ≠ lv b → (γ ⬝ J) t b = 0 := by
    intro t b h
    generalize P * β = A at hA hAB hBA
    generalize γ * J = B at hAB hBA
    have h1 : diagonal (fun a => if lv a = lv b then (1 : k) else 0) * A =
        A * diagonal (fun r => if lw r = lv b then (1 : k) else 0) := by
      ext a r
      rw [diagonal_mul, mul_diagonal]
      by_cases e : lv a = lw r
      · rw [e, mul_comm]
      · rw [hA a r e, mul_zero, zero_mul]
    have h2 : B * diagonal (fun a => if lv a = lv b then (1 : k) else 0) =
        diagonal (fun r => if lw r = lv b then (1 : k) else 0) * B := by
      rw [← Matrix.mul_one (B * _), ← hAB, ← Matrix.mul_assoc, Matrix.mul_assoc B, h1, ← Matrix.mul_assoc, hBA,
        Matrix.one_mul]
    have h3 := congrFun (congrFun h2 t) b
    rwa [diagonal_mul, mul_diagonal, if_pos rfl, if_neg h, mul_one, zero_mul] at h3
  have e : P * (β * q * γ - 1) * J = (P * β) * (q - 1) * (γ * J) := by
    rw [← hβγ]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul]
  rw [e, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases ht : lw t = lv b
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro r _
    by_cases hr : lv a = lw r
    · rw [Matrix.sub_apply, hq r t (by omega), sub_self, mul_zero]
    · rw [hA a r hr, zero_mul]
  · rw [hB t b ht, mul_zero]

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

def wl (σ r : ℕ) : Fin σ ⊕ (Fin r ⊕ Fin σ) → ℕ :=
  Sum.elim (fun i => i.val + 1) (Sum.elim (fun _ => σ + 1) fun i => 2 * σ - i.val + 1)

def wJ {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) : Matrix (Fin V.rank) (Fin σ ⊕ (Fin V₀.rank ⊕ Fin σ)) D.host.E :=
  fromCols d.e (fromCols d.i₀ d.e')

noncomputable def wP {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) :
    Matrix (Fin σ ⊕ (Fin V₀.rank ⊕ Fin σ)) (Fin V.rank) D.host.E :=
  fromRows d.qX (fromRows d.q0 d.qY)

/- English proof (translation)
Rewrite using `[wJ, wP, fromCols_mul_fromRows, fromCols_mul_fromRows, ← add_assoc, d.sum_eq_one_rat]`.
-/
theorem wJ_wP {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) : wJ d * wP d = 1 := by
  rw [wJ, wP, fromCols_mul_fromRows, fromCols_mul_fromRows, ← add_assoc, d.sum_eq_one_rat]

/- English proof (translation)
The claim follows from `(Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [← d.rank_add]; ring)).1 (wJ_wP d)`.
-/
theorem wP_wJ {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) : wP d * wJ d = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [← d.rank_add]; ring)).1 (wJ_wP d)

/- English proof (translation)
Take `⟨hc, h1, h2, h3, h4⟩` from `h`. Break down `r with a | j` into its components or cases. Use `⟨Sum.elim 0 (Sum.elim (fun w => (B.o.iA.map (Witness.prH p) * FA.β) w a) 0), ?_, fun u => ?_⟩` and prove the remaining obligations. Introduce and unpack `(z | z | z) hz`. Both sides reduce to the same expression.

Conclude with `absurd rfl hz`. Both sides reduce to the same expression. Rewrite using `[h1]`. Express the relevant statement in the definitionally equal form `((B.d.i₀ * B.o.iA).map (Witness.prH p) * FA.β) u a = _`. Rewrite using `[Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply]`.

Simplify using `[wJ]`. Establish `hj` using `j.isLt`. Break down `lt_trichotomy j.val σ with hlt | heq | hgt` into its components or cases. Use `⟨Pi.single (Sum.inl ⟨j.val, hlt⟩) (s * p.xi ^ (σ - j.val)), fun z hz => Pi.single_eq_of_ne ?_ _, fun u => ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `hz rfl`. Rewrite using `[h2 ⟨j.val, hlt⟩ j rfl, Finset.sum_eq_single (Sum.inl ⟨j.val, hlt⟩), Pi.single_eq_same, mul_comm]`. Both sides reduce to the same expression. Introduce `b _ hb`. Rewrite using `[Pi.single_eq_of_ne hb, mul_zero]`.

Simplify using the standard rewrite rules. Use `⟨Sum.elim 0 (Sum.elim (fun w => s * Witness.prH p (vecB B.o B.ζ w)) 0), ?_, fun u => ?_⟩` and prove the remaining obligations. Introduce and unpack `(z | z | z) hz`. Both sides reduce to the same expression. Conclude with `absurd (by simp [wl, lev, heq]) hz`.

Both sides reduce to the same expression. Rewrite using `[h3 j heq]`. Express the relevant statement in the definitionally equal form `s * Witness.prH p (∑ w, B.d.i₀ u w * vecB B.o B.ζ w) = _`. Rewrite using `[map_sum, Finset.mul_sum]`. Simplify using `[wJ, mul_left_comm]`.

Establish `hi : 2 * σ - j.val < σ` using `by omega`. Use `⟨Pi.single (Sum.inr (Sum.inr ⟨_, hi⟩)) (s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (σ - 1 - (2 * σ - j.val))), fun z hz => Pi.single_eq_of_ne ?_ _, fun u => ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hz (by simp only [wl, lev, Sum.elim_inr]; omega)`. Rewrite using `[h4 ⟨_, hi⟩ j (by simp only; omega), Finset.sum_eq_single (Sum.inr (Sum.inr ⟨_, hi⟩)), Pi.single_eq_same, mul_comm]`.

Both sides reduce to the same expression. Introduce `b _ hb`. Rewrite using `[Pi.single_eq_of_ne hb, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem frame_cols {σ : ℕ} (B : BesLev D σ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)) (h : p.IsBesFrame B s FA FV) (r : n ⊕ Fin c) :
    ∃ x : Fin σ ⊕ (Fin B.V₀.rank ⊕ Fin σ) → k, (∀ z, wl σ _ z ≠ lev (σ + 1) r → x z = 0) ∧
      ∀ u, FV.β u r = ∑ z, (wJ B.d).map (Witness.prH p) u z * x z := by
  obtain ⟨hc, h1, h2, h3, h4⟩ := h
  rcases r with a | j
  · refine ⟨Sum.elim 0 (Sum.elim (fun w => (B.o.iA.map (Witness.prH p) * FA.β) w a) 0), ?_, fun u => ?_⟩
    · rintro (z | z | z) hz
      · rfl
      · exact absurd rfl hz
      · rfl
    · rw [h1]
      change ((B.d.i₀ * B.o.iA).map (Witness.prH p) * FA.β) u a = _
      rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply]
      simp [wJ]
  · have hj := j.isLt
    rcases lt_trichotomy j.val σ with hlt | heq | hgt
    · refine ⟨Pi.single (Sum.inl ⟨j.val, hlt⟩) (s * p.xi ^ (σ - j.val)), fun z hz => Pi.single_eq_of_ne ?_ _, fun u => ?_⟩
      · rintro rfl
        exact hz rfl
      · rw [h2 ⟨j.val, hlt⟩ j rfl, Finset.sum_eq_single (Sum.inl ⟨j.val, hlt⟩), Pi.single_eq_same, mul_comm]
        · rfl
        · intro b _ hb
          rw [Pi.single_eq_of_ne hb, mul_zero]
        · simp
    · refine ⟨Sum.elim 0 (Sum.elim (fun w => s * Witness.prH p (vecB B.o B.ζ w)) 0), ?_, fun u => ?_⟩
      · rintro (z | z | z) hz
        · rfl
        · exact absurd (by simp [wl, lev, heq]) hz
        · rfl
      · rw [h3 j heq]
        change s * Witness.prH p (∑ w, B.d.i₀ u w * vecB B.o B.ζ w) = _
        rw [map_sum, Finset.mul_sum]
        simp [wJ, mul_left_comm]
    · have hi : 2 * σ - j.val < σ := by omega
      refine ⟨Pi.single (Sum.inr (Sum.inr ⟨_, hi⟩))
        (s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (σ - 1 - (2 * σ - j.val))), fun z hz => Pi.single_eq_of_ne ?_ _, fun u => ?_⟩
      · rintro rfl
        exact hz (by simp only [wl, lev, Sum.elim_inr]; omega)
      · rw [h4 ⟨_, hi⟩ j (by simp only; omega), Finset.sum_eq_single (Sum.inr (Sum.inr ⟨_, hi⟩)), Pi.single_eq_same, mul_comm]
        · rfl
        · intro b _ hb
          rw [Pi.single_eq_of_ne hb, mul_zero]
        · simp

/- English proof (translation)
Establish `h1 : (wP B.d).map (Witness.prH p) * (wJ B.d).map (Witness.prH p) = 1`. Rewrite using `[← Matrix.map_mul, wP_wJ, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `h2 : (wJ B.d).map (Witness.prH p) * (wP B.d).map (Witness.prH p) = 1`. Rewrite using `[← Matrix.map_mul, wJ_wP, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `key` using `conj_vanish (wl σ _) (lev (σ + 1)) _ _ FV.β FV.γ h1 h2 FV.βγ FV.γβ (fun a r har => by`.

Take `⟨x, hx, hβ⟩` from `frame_cols p B s FA FV h r`. Establish `: (((wP B.d).map (Witness.prH p)) ⬝ FV.β) a r = (((wP B.d).map (Witness.prH p) * (wJ B.d).map (Witness.prH p)) *ᵥ x) a`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun u _ => by rw [hβ]; rfl`. Rewrite using `[this, h1, Matrix.one_mulVec, hx a har]) q.val ((GlobalTheory.RootEx.Radical.mem_N_iff q).1 hq) a b hab`.

Rewrite using `[← key, ← hM, ← Matrix.map_apply (f := p.π), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub p.π), Matrix.map_one _ (map_zero _) (map_one _)]`. Both sides reduce to the same expression.
-/
theorem comp_vanish {σ : ℕ} (B : BesLev D σ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)) (h : p.IsBesFrame B s FA FV)
    (M : Mx D B.V.rank B.V.rank) (q : GL (n ⊕ Fin c) k) (hq : q ∈ N k n c (σ + 1))
    (hM : M.map p.π = FV.β * q.val * FV.γ) (a b : Fin σ ⊕ (Fin B.V₀.rank ⊕ Fin σ)) (hab : wl σ _ b ≤ wl σ _ a) :
    p.π (((wP B.d).map (incA D) ⬝ (M - 1) ⬝ (wJ B.d).map (incA D)) a b) = 0 := by
  have h1 : (wP B.d).map (Witness.prH p) * (wJ B.d).map (Witness.prH p) = 1 := by
    rw [← Matrix.map_mul, wP_wJ, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (wJ B.d).map (Witness.prH p) * (wP B.d).map (Witness.prH p) = 1 := by
    rw [← Matrix.map_mul, wJ_wP, Matrix.map_one _ (map_zero _) (map_one _)]
  have key := conj_vanish (wl σ _) (lev (σ + 1)) _ _ FV.β FV.γ h1 h2 FV.βγ FV.γβ (fun a r har => by
    obtain ⟨x, hx, hβ⟩ := frame_cols p B s FA FV h r
    have : (((wP B.d).map (Witness.prH p)) ⬝ FV.β) a r =
        (((wP B.d).map (Witness.prH p) * (wJ B.d).map (Witness.prH p)) *ᵥ x) a := by
      rw [← Matrix.mulVec_mulVec, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun u _ => by rw [hβ]; rfl
    rw [this, h1, Matrix.one_mulVec, hx a har]) q.val ((GlobalTheory.RootEx.Radical.mem_N_iff q).1 hq) a b hab
  rw [← key, ← hM, ← Matrix.map_apply (f := p.π), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub p.π),
    Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

/- English proof (translation)
Establish `e1 : (p.e + cA D p.e) • (mt V g - 1) = mt V g - 1` using `Matrix.ext hg`. Establish `e2 : (p.e + cA D p.e) * (P ⬝ (mt V g - 1) ⬝ J) i j = (P ⬝ (mt V g - 1) ⬝ J) i j` using `by conv_rhs => rw [← e1, Matrix.mul_smul, Matrix.smul_mul]`. Both sides reduce to the same expression. Establish `e3 : (adj J ⬝ gA V) ⬝ (mt V g⁻¹ - 1) ⬝ (giA V ⬝ adj P) = adj (P ⬝ (mt V g - 1) ⬝ J)`. Simplify using `only [mt_inv, adj_mul, adj_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, gA_giA_cancel, Matrix.one_mul]`.

Rewrite `h2` using `[e3]`. Express the relevant statement in the definitionally equal form `p.π (cA D ((P ⬝ (mt V g - 1) ⬝ J) i j)) = 0 at h2`. Generalize the expression as in `(P ⬝ (mt V g - 1) ⬝ J) i j = x at h1 h2 e2`. Establish `a1 : p.e * x = 0` using `by rw [← p.ι_π, h1, map_zero]`. Establish `a2 : p.e * cA D x = 0` using `by rw [← p.ι_π, h2, map_zero]`.

Establish `a3 : cA D p.e * x = 0`. Use `congrArg (cA D) a2` as an intermediate fact. Rewrite `this` using `[map_mul, cA_cA, map_zero]`. Then use the resulting hypothesis. Rewrite using `[← e2, add_mul, a1, a3, add_zero]`.
-/
theorem entry_zero {V : HSp D} {g : GA D V} (hg : SuppAt p.e V g) {l m : ℕ} (P : Mx D l V.rank) (J : Mx D V.rank m) (i j)
    (h1 : p.π ((P ⬝ (mt V g - 1) ⬝ J) i j) = 0)
    (h2 : p.π (((adj J ⬝ gA V) ⬝ (mt V g⁻¹ - 1) ⬝ (giA V ⬝ adj P)) j i) = 0) : (P ⬝ (mt V g - 1) ⬝ J) i j = 0 := by
  have e1 : (p.e + cA D p.e) • (mt V g - 1) = mt V g - 1 := Matrix.ext hg
  have e2 : (p.e + cA D p.e) * (P ⬝ (mt V g - 1) ⬝ J) i j = (P ⬝ (mt V g - 1) ⬝ J) i j := by
    conv_rhs => rw [← e1, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have e3 : (adj J ⬝ gA V) ⬝ (mt V g⁻¹ - 1) ⬝ (giA V ⬝ adj P) = adj (P ⬝ (mt V g - 1) ⬝ J) := by
    simp only [mt_inv, adj_mul, adj_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, gA_giA_cancel,
      Matrix.one_mul]
  rw [e3] at h2
  change p.π (cA D ((P ⬝ (mt V g - 1) ⬝ J) i j)) = 0 at h2
  generalize (P ⬝ (mt V g - 1) ⬝ J) i j = x at h1 h2 e2
  have a1 : p.e * x = 0 := by rw [← p.ι_π, h1, map_zero]
  have a2 : p.e * cA D x = 0 := by rw [← p.ι_π, h2, map_zero]
  have a3 : cA D p.e * x = 0 := by
    have := congrArg (cA D) a2
    rwa [map_mul, cA_cA, map_zero] at this
  rw [← e2, add_mul, a1, a3, add_zero]

/- English proof (translation)
Take `⟨L, rfl⟩ : ∃ L, M = 1 + L` from `⟨M - 1, by abel⟩`. Rewrite `zXX`, `z0X`, `zYX`, `z00`, `zY0` using `[add_sub_cancel_left]`. Establish `cX : L * jX = jX * (pX * L * jX)` using `by conv_lhs => rw [← Matrix.one_mul L, ← h]`. Simplify using `only [Matrix.mul_assoc] at z0X zYX`. Simplify using `only [Matrix.add_mul, Matrix.mul_assoc, z0X, zYX, Matrix.mul_zero, add_zero]`.

Establish `c0 : L * j0 = jX * (pX * L * j0)` using `by conv_lhs => rw [← Matrix.one_mul L, ← h]`. Simplify using `only [Matrix.mul_assoc] at z00 zY0`. Simplify using `only [Matrix.add_mul, Matrix.mul_assoc, z00, zY0, Matrix.mul_zero, add_zero]`. Use `⟨⟨_, zXX, by rw [← cX, Matrix.add_mul, Matrix.one_mul]⟩, fun y hy => ?_⟩` and prove the remaining obligations. Use `⟨(pX * L * jX) *ᵥ (pX *ᵥ y) + (pX * L * j0) *ᵥ (p0 *ᵥ y), ?_⟩` and prove the remaining obligations.

Establish `hy' : y = jX *ᵥ (pX *ᵥ y) + j0 *ᵥ (p0 *ᵥ y)` using `by conv_lhs => rw [← Matrix.one_mulVec y, ← h]`. Rewrite using `[Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero, add_zero]`. Rewrite using `[Matrix.mulVec_add, Matrix.mulVec_mulVec _ jX, Matrix.mulVec_mulVec _ jX, ← cX, ← c0, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← hy', Matrix.add_mulVec, Matrix.one_mulVec]`.
-/
theorem unip_of_blocks {R : Type} [CommRing R] {m r σ : ℕ} (jX jY : Matrix (Fin m) (Fin σ) R) (j0 : Matrix (Fin m) (Fin r) R)
    (pX pY : Matrix (Fin σ) (Fin m) R) (p0 : Matrix (Fin r) (Fin m) R) (h : jX * pX + j0 * p0 + jY * pY = 1)
    (M : Matrix (Fin m) (Fin m) R) (zXX : GlobalTheory.BesselChar.StrictUp (pX * (M - 1) * jX)) (z0X : p0 * (M - 1) * jX = 0)
    (zYX : pY * (M - 1) * jX = 0) (z00 : p0 * (M - 1) * j0 = 0) (zY0 : pY * (M - 1) * j0 = 0) :
    GlobalTheory.BesselChar.Unip jX pY M := by
  obtain ⟨L, rfl⟩ : ∃ L, M = 1 + L := ⟨M - 1, by abel⟩
  rw [add_sub_cancel_left] at zXX z0X zYX z00 zY0
  have cX : L * jX = jX * (pX * L * jX) := by
    conv_lhs => rw [← Matrix.one_mul L, ← h]
    simp only [Matrix.mul_assoc] at z0X zYX
    simp only [Matrix.add_mul, Matrix.mul_assoc, z0X, zYX, Matrix.mul_zero, add_zero]
  have c0 : L * j0 = jX * (pX * L * j0) := by
    conv_lhs => rw [← Matrix.one_mul L, ← h]
    simp only [Matrix.mul_assoc] at z00 zY0
    simp only [Matrix.add_mul, Matrix.mul_assoc, z00, zY0, Matrix.mul_zero, add_zero]
  refine ⟨⟨_, zXX, by rw [← cX, Matrix.add_mul, Matrix.one_mul]⟩, fun y hy => ?_⟩
  refine ⟨(pX * L * jX) *ᵥ (pX *ᵥ y) + (pX * L * j0) *ᵥ (p0 *ᵥ y), ?_⟩
  have hy' : y = jX *ᵥ (pX *ᵥ y) + j0 *ᵥ (p0 *ᵥ y) := by
    conv_lhs => rw [← Matrix.one_mulVec y, ← h]
    rw [Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hy, Matrix.mulVec_zero, add_zero]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec _ jX, Matrix.mulVec_mulVec _ jX, ← cX, ← c0,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← hy', Matrix.add_mulVec, Matrix.one_mulVec]

/- English proof (translation)
Unfold `flagN`. Rewrite using `[GlobalTheory.BesselChar.mem_NFlag_iff V d.e (isIsoSub_e d).1]`. Conclude with `unip_of_blocks d.jX d.jY d.j0 d.pX d.pY d.p0 d.sum_eq_one _ zXX z0X zYX z00 zY0`.
-/
theorem mem_of_blocks {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) (g : GA D V)
    (zXX : GlobalTheory.BesselChar.StrictUp (d.pX ⬝ (mt V g - 1) ⬝ d.jX)) (z0X : d.p0 ⬝ (mt V g - 1) ⬝ d.jX = 0)
    (zYX : d.pY ⬝ (mt V g - 1) ⬝ d.jX = 0) (z00 : d.p0 ⬝ (mt V g - 1) ⬝ d.j0 = 0)
    (zY0 : d.pY ⬝ (mt V g - 1) ⬝ d.j0 = 0) : g ∈ flagN d := by
  unfold flagN
  rw [GlobalTheory.BesselChar.mem_NFlag_iff V d.e (isIsoSub_e d).1]
  exact unip_of_blocks d.jX d.jY d.j0 d.pX d.pY d.p0 d.sum_eq_one _ zXX z0X zYX z00 zY0

/- English proof (translation)
Apply the tactic sequence `refine ⟨fun i j h => W (Sum.inl i) (Sum.inl j) ?_, Matrix.ext fun i j => W (Sum.inr (Sum.inl i)) (Sum.inl j) ?_, Matrix.ext fun i j => W (Sum.inr (Sum.inr i)) (Sum.inl j) ?_, Matrix.ext fun i j => W (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) ?_, Matrix.ext fun i j => W (Sum.inr …`. Apply the tactic sequence `simp only [wl, Sum.elim_inr, Sum.elim_inl] <;> omega`.
-/
theorem blocks_vanish {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) (M : Mx D V.rank V.rank)
    (W : ∀ a b, wl σ _ b ≤ wl σ _ a → p.π (((wP d).map (incA D) ⬝ M ⬝ (wJ d).map (incA D)) a b) = 0) :
    (∀ i j, j ≤ i → p.π ((d.pX ⬝ M ⬝ d.jX) i j) = 0) ∧ (d.p0 ⬝ M ⬝ d.jX).map p.π = 0 ∧ (d.pY ⬝ M ⬝ d.jX).map p.π = 0 ∧
      (d.p0 ⬝ M ⬝ d.j0).map p.π = 0 ∧ (d.pY ⬝ M ⬝ d.j0).map p.π = 0 ∧
      ∀ i j, i ≤ j → p.π ((d.pY ⬝ M ⬝ d.jY) i j) = 0 := by
  refine ⟨fun i j h => W (Sum.inl i) (Sum.inl j) ?_, Matrix.ext fun i j => W (Sum.inr (Sum.inl i)) (Sum.inl j) ?_,
    Matrix.ext fun i j => W (Sum.inr (Sum.inr i)) (Sum.inl j) ?_,
    Matrix.ext fun i j => W (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) ?_,
    Matrix.ext fun i j => W (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) ?_,
    fun i j h => W (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) ?_⟩ <;>
  simp only [wl, Sum.elim_inr, Sum.elim_inl] <;> omega

/- English proof (translation)
Introduce `D k _ _ _ _ p σ B s n _ _ c FA FV hF g q hq hg`. Take `⟨hS, hg⟩` from `hg`. Establish `hg' : (mt B.V g⁻¹).map p.π = FV.β * (q⁻¹).val * FV.γ`. Establish `h1 : (mt B.V g⁻¹).map p.π * (mt B.V g).map p.π = 1`. Rewrite using `[← Matrix.map_mul, GlobalTheory.MixModel.mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `h2 : (FV.β * q.val * FV.γ) * (FV.β * (q⁻¹).val * FV.γ) = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc FV.β (q⁻¹).val, ← Matrix.mul_assoc FV.γ, FV.γβ, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.mul_assoc q.val, Units.mul_inv, Matrix.one_mul, FV.βγ]`. Rewrite using `[← Matrix.mul_one (Matrix.map _ _), ← h2, ← Matrix.mul_assoc _ (FV.β * q.val * FV.γ), ← hg, h1, Matrix.one_mul]`. Take `⟨XX, OX, YX, OO, YO, -⟩` from `blocks_vanish p B.d _ (comp_vanish p B s FA FV hF _ q hq hg)`. Take `⟨-, OX', YX', OO', YO', YY'⟩` from `blocks_vanish p B.d _ (comp_vanish p B s FA FV hF _ q⁻¹ (inv_mem hq) hg')`.

Generalize the expression as in `B.d = d at *`. Establish `aX : giA B.V ⬝ adj d.pX = d.jY` using `by rw [d.pX_eq, adj_mul, adj_adj, adj_gA, giA_gA_cancel]`. Establish `aY : giA B.V ⬝ adj d.pY = d.jX` using `by rw [d.pY_eq, adj_mul, adj_adj, adj_gA, giA_gA_cancel]`. Establish `a0 : giA B.V ⬝ adj d.p0 = d.j0 ⬝ giA B.V₀`. Rewrite using `[d.p0_eq, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_gA_cancel]`.

Establish `b0 : adj d.j0 ⬝ gA B.V = gA B.V₀ ⬝ d.p0` using `by rw [d.p0_eq, gA_giA_cancel]`. Establish `ev : ∀ {l m : ℕ} {x : Mx D l m}, x.map p.π = 0 → ∀ i j, p.π (x i j) = 0` using `fun h i j => congrFun (congrFun h i) j`. Use `mem_of_blocks d g (fun i j hij => entry_zero p hS _ _ i j (XX i j hij) ?_) (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev OX i j) ?_) (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev YX i j) ?_) (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev OO i j) ?_) (Matrix.ext fun …` and prove the remaining obligations. Rewrite using `[aX, ← d.pY_eq]`. Conclude with `YY' j i hij`.

Use `ev ?_ j i` and prove the remaining obligations. Rewrite using `[a0, ← d.pY_eq, ← Matrix.mul_assoc, Matrix.map_mul, YO', Matrix.zero_mul]`. Rewrite using `[aY, ← d.pY_eq]`. Conclude with `ev YX' j i`. Use `ev ?_ j i` and prove the remaining obligations.

Rewrite using `[a0, b0, ← Matrix.mul_assoc, Matrix.mul_assoc (gA _), Matrix.mul_assoc (gA _), Matrix.map_mul, Matrix.map_mul, OO', Matrix.mul_zero, Matrix.zero_mul]`. Use `ev ?_ j i` and prove the remaining obligations. Rewrite using `[aY, b0, Matrix.mul_assoc (gA _), Matrix.mul_assoc (gA _), Matrix.map_mul, OX', Matrix.mul_zero]`.
-/
theorem mem_flagN : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (σ : ℕ) (B : BesLev D σ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA FV → ∀ (g : GA D B.V) (q : GL (n ⊕ Fin c) k), q ∈ N k n c (σ + 1) → p.IsLoc FV g q → g ∈ flagN B.d := by
  intro D k _ _ _ _ p σ B s n _ _ c FA FV hF g q hq hg
  obtain ⟨hS, hg⟩ := hg
  have hg' : (mt B.V g⁻¹).map p.π = FV.β * (q⁻¹).val * FV.γ := by
    have h1 : (mt B.V g⁻¹).map p.π * (mt B.V g).map p.π = 1 := by
      rw [← Matrix.map_mul, GlobalTheory.MixModel.mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : (FV.β * q.val * FV.γ) * (FV.β * (q⁻¹).val * FV.γ) = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc FV.β (q⁻¹).val, ← Matrix.mul_assoc FV.γ, FV.γβ, Matrix.one_mul,
        Matrix.mul_assoc, ← Matrix.mul_assoc q.val, Units.mul_inv, Matrix.one_mul, FV.βγ]
    rw [← Matrix.mul_one (Matrix.map _ _), ← h2, ← Matrix.mul_assoc _ (FV.β * q.val * FV.γ), ← hg, h1, Matrix.one_mul]
  obtain ⟨XX, OX, YX, OO, YO, -⟩ := blocks_vanish p B.d _ (comp_vanish p B s FA FV hF _ q hq hg)
  obtain ⟨-, OX', YX', OO', YO', YY'⟩ := blocks_vanish p B.d _ (comp_vanish p B s FA FV hF _ q⁻¹ (inv_mem hq) hg')
  generalize B.d = d at *
  have aX : giA B.V ⬝ adj d.pX = d.jY := by rw [d.pX_eq, adj_mul, adj_adj, adj_gA, giA_gA_cancel]
  have aY : giA B.V ⬝ adj d.pY = d.jX := by rw [d.pY_eq, adj_mul, adj_adj, adj_gA, giA_gA_cancel]
  have a0 : giA B.V ⬝ adj d.p0 = d.j0 ⬝ giA B.V₀ := by
    rw [d.p0_eq, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_gA_cancel]
  have b0 : adj d.j0 ⬝ gA B.V = gA B.V₀ ⬝ d.p0 := by rw [d.p0_eq, gA_giA_cancel]
  have ev : ∀ {l m : ℕ} {x : Mx D l m}, x.map p.π = 0 → ∀ i j, p.π (x i j) = 0 := fun h i j => congrFun (congrFun h i) j
  refine mem_of_blocks d g (fun i j hij => entry_zero p hS _ _ i j (XX i j hij) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev OX i j) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev YX i j) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev OO i j) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev YO i j) ?_)
  · rw [aX, ← d.pY_eq]
    exact YY' j i hij
  · refine ev ?_ j i
    rw [a0, ← d.pY_eq, ← Matrix.mul_assoc, Matrix.map_mul, YO', Matrix.zero_mul]
  · rw [aY, ← d.pY_eq]
    exact ev YX' j i
  · refine ev ?_ j i
    rw [a0, b0, ← Matrix.mul_assoc, Matrix.mul_assoc (gA _), Matrix.mul_assoc (gA _),
      Matrix.map_mul, Matrix.map_mul, OO', Matrix.mul_zero, Matrix.zero_mul]
  · refine ev ?_ j i
    rw [aY, b0, Matrix.mul_assoc (gA _), Matrix.mul_assoc (gA _), Matrix.map_mul, OX', Matrix.mul_zero]

end GlobalTheory.LocFlag
