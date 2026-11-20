import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ConjModelCast

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.SecWt

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (conjEmb Coeff Level)

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}

/- English proof (translation)
Introduce `τ τ' h` and use `by ext a have h1 : σ (embF c τ a) = σ (embF c τ' a) := congrArg (fun f : E →+* ℂ => f a) h exact congrArg Subtype.val (σ.injective h1)`.
-/
theorem relab_inj (c : Coeff l) (σ : c.F →+* ℂ) : Function.Injective (relab (E := E) c σ) := fun τ τ' h => by
  ext a
  have h1 : σ (embF c τ a) = σ (embF c τ' a) := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective h1)

/- English proof (translation)
Use extensionality with `a`. Establish `h1 : embF c (conjEmb τ) a = embF c τ (IsCMField.complexConj E a)` using `Subtype.ext (IsCMField.complexEmbedding_complexConj E τ a).symm`. Use `show σ (embF c (conjEmb τ) a) = starRingEnd ℂ (relab c σ τ a)`. Rewrite using `[h1]`. Conclude with `IsCMField.complexEmbedding_complexConj E (relab c σ τ) a`.
-/
theorem relab_conjEmb (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) :
    relab c σ (conjEmb τ) = conjEmb (relab c σ τ) := by
  ext a
  have h1 : embF c (conjEmb τ) a = embF c τ (IsCMField.complexConj E a) :=
    Subtype.ext (IsCMField.complexEmbedding_complexConj E τ a).symm
  show σ (embF c (conjEmb τ) a) = starRingEnd ℂ (relab c σ τ a)
  rw [h1]
  exact IsCMField.complexEmbedding_complexConj E (relab c σ τ) a

/- English proof (translation)
Introduce `e`. Establish `him : H.rt0.im = 0` using `Complex.conj_eq_iff_im.1 e`. Establish `hre` using `congrArg Complex.re H.sqrt_neg_disc_sq`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Simplify using `only [sq, Complex.mul_re, Complex.neg_re, Complex.natCast_re, him] at hre`.

Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`.
-/
theorem conj_cmHostRoot_ne_self : (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro e
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 e
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp only [sq, Complex.mul_re, Complex.neg_re, Complex.natCast_re, him] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

end

/- English proof (translation)
Introduce `_ _ h` and use `D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))`.
-/
theorem tauE_inj (D : D7) : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

/- English proof (translation)
Introduce `a b h` and use `by ext x exact star_injective (RingHom.congr_fun h x)`.
-/
theorem conjEmb_inj {E : Type} [Field E] : Function.Injective (conjEmb (E := E)) := fun a b h => by
  ext x
  exact star_injective (RingHom.congr_fun h x)

/- English proof (translation)
Unfold `wtA`. Simplify using `only [show DV.tauEmb D = tauE D from rfl]`. Rewrite using `[Finset.sum_eq_single s]`. Rewrite using `[if_pos rfl, if_neg (hne s s)]`. Both sides reduce to the same expression.

Introduce `t _ ht`. Rewrite using `[if_neg (fun h => ht (tauE_inj D h).symm), if_neg (hne s t), add_zero]`. Simplify using the standard rewrite rules.
-/
theorem wtA_pos {D : D7} (hne : ∀ s t, tauE D s ≠ conjEmb (tauE D t)) {j : ℕ} (w : WeightFamilies.Wt D j) (s : D.what₂.Tau) (n : ℕ) :
    wtA w (tauE D s, n) = ext0 (w.aP s) n := by
  unfold wtA
  simp only [show DV.tauEmb D = tauE D from rfl]
  rw [Finset.sum_eq_single s]
  · rw [if_pos rfl, if_neg (hne s s)]; rfl
  · intro t _ ht
    rw [if_neg (fun h => ht (tauE_inj D h).symm), if_neg (hne s t), add_zero]
  · simp

/- English proof (translation)
Unfold `wtA`. Simplify using `only [show DV.tauEmb D = tauE D from rfl]`. Rewrite using `[Finset.sum_eq_single s]`. Rewrite using `[if_neg (fun h => hne s s (Eq.symm h)), if_pos rfl, zero_add]`. Introduce `t _ ht`.

Rewrite using `[if_neg (fun h => hne t s (Eq.symm h)), if_neg (fun h => ht (tauE_inj D (conjEmb_inj h)).symm), add_zero]`. Simplify using the standard rewrite rules.
-/
theorem wtA_neg {D : D7} (hne : ∀ s t, tauE D s ≠ conjEmb (tauE D t)) {j : ℕ} (w : WeightFamilies.Wt D j) (s : D.what₂.Tau) (n : ℕ) :
    wtA w (conjEmb (tauE D s), n) = ext0 (w.aM s) n := by
  unfold wtA
  simp only [show DV.tauEmb D = tauE D from rfl]
  rw [Finset.sum_eq_single s]
  · rw [if_neg (fun h => hne s s (Eq.symm h)), if_pos rfl, zero_add]
  · intro t _ ht
    rw [if_neg (fun h => hne t s (Eq.symm h)), if_neg (fun h => ht (tauE_inj D (conjEmb_inj h)).symm), add_zero]
  · simp

/- English proof (translation)
Establish `hk` using `D.R.m_add_three_le_k`. Establish `hi` using `i.2`. Establish `h3` using `Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) (p - 1 - n) n (by simp only [Ranks.r]; omega)`. Establish `hl : Formalism.L2.NTheta.lamAt (D.hc τ) (n + (p - 1 - n)) = -(D.hc τ).b i`. Unfold `Formalism.L2.NTheta.lamAt`.

Rewrite using `[dif_neg (by omega), dif_pos (by omega)]`. Use `congr 2`. Conclude with `Fin.ext (by simp only; omega)`. Establish `hc : ((p - 1 - n : ℕ) : ℚ) = (p : ℚ) - (n + 1)`. Rewrite using `[Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring`.

Rewrite `h3` using `[hl, hc]`. Establish `g` using `(D.hc τ).gap_be i`. Take `⟨z1, h1⟩` from `Formalism.L2.NTheta.lamAt_int (D.hc τ) n`. Take `⟨z2, h2⟩` from `(D.hc τ).e_int i`. Take `⟨s, hs⟩` from `D.R.t_odd`.

Establish `ht : (D.R.t : ℚ) = 2 * s + 1` using `by exact_mod_cast hs`. Establish `hz : Formalism.L2.NTheta.lamAt (D.hc τ) n + (D.hc τ).e i - ((p : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 = ((z1 + z2 - (p - (n + 1)) - (s + 1) : ℤ) : ℚ)`. Rewrite using `[h1, h2, ht]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h0 : (0 : ℤ) ≤ z1 + z2 - (p - (n + 1)) - (s + 1)`. Establish `: (0 : ℚ) ≤ ((z1 + z2 - (p - (n + 1)) - (s + 1) : ℤ) : ℚ)` using `by rw [← hz]; linarith`. Conclude with `this` after adjusting the coercions. Unfold `aPl`. Rewrite using `[if_pos hn, hz, Int.floor_intCast]`.

Conclude with `Int.toNat_of_nonneg h0` after adjusting the coercions.
-/
theorem aPl_cast (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (p n : ℕ) (hp : p = D.R.k + i) (hn : n < p) :
    (aPl D i p τ n : ℚ) =
      Formalism.L2.NTheta.lamAt (D.hc τ) n + (D.hc τ).e i - ((p : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have h3 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) (p - 1 - n) n (by simp only [Ranks.r]; omega)
  have hl : Formalism.L2.NTheta.lamAt (D.hc τ) (n + (p - 1 - n)) = -(D.hc τ).b i := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dif_neg (by omega), dif_pos (by omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  have hc : ((p - 1 - n : ℕ) : ℚ) = (p : ℚ) - (n + 1) := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
  rw [hl, hc] at h3
  have g := (D.hc τ).gap_be i
  obtain ⟨z1, h1⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) n
  obtain ⟨z2, h2⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have ht : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  have hz : Formalism.L2.NTheta.lamAt (D.hc τ) n + (D.hc τ).e i - ((p : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 =
      ((z1 + z2 - (p - (n + 1)) - (s + 1) : ℤ) : ℚ) := by
    rw [h1, h2, ht]; push_cast; ring
  have h0 : (0 : ℤ) ≤ z1 + z2 - (p - (n + 1)) - (s + 1) := by
    have : (0 : ℚ) ≤ ((z1 + z2 - (p - (n + 1)) - (s + 1) : ℤ) : ℚ) := by rw [← hz]; linarith
    exact_mod_cast this
  unfold aPl
  rw [if_pos hn, hz, Int.floor_intCast]
  exact_mod_cast Int.toNat_of_nonneg h0

/- English proof (translation)
Establish `hk` using `D.R.m_add_three_le_k`. Establish `hi` using `i.2`. Establish `h3` using `Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) c p (by simp only [Ranks.r]; omega)`. Establish `hm : (i : ℕ) + 1 < D.R.m` using `by omega`. Establish `hl : Formalism.L2.NTheta.lamAt (D.hc τ) p = -(D.hc τ).b ⟨i + 1, hm⟩`.

Unfold `Formalism.L2.NTheta.lamAt`. Rewrite using `[dif_neg (by omega), dif_pos (by omega)]`. Use `congr 2`. Conclude with `Fin.ext (by simp only; omega)`. Rewrite `h3` using `[hl]`.

Establish `g` using `(D.hc τ).gap_eb i hm`. Take `⟨z1, h1⟩` from `Formalism.L2.NTheta.lamAt_int (D.hc τ) (p + c)`. Take `⟨z2, h2⟩` from `(D.hc τ).e_int i`. Take `⟨s, hs⟩` from `D.R.t_odd`. Establish `ht : (D.R.t : ℚ) = 2 * s + 1` using `by exact_mod_cast hs`.

Establish `hz : -((D.hc τ).e i + Formalism.L2.NTheta.lamAt (D.hc τ) (p + c) + ((c : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2) = ((-(z2 + z1 + (c + 1) + s) : ℤ) : ℚ)`. Rewrite using `[h1, h2, ht]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : (0 : ℤ) ≤ -(z2 + z1 + (c + 1) + s)`.

Establish `: (0 : ℚ) ≤ ((-(z2 + z1 + (c + 1) + s) : ℤ) : ℚ)` using `by rw [← hz]; linarith`. Conclude with `this` after adjusting the coercions. Unfold `aMi`. Rewrite using `[if_pos (by omega), show q - (q - 1 - c) = c + 1 by omega, show p + (c + 1) - 1 = p + c by omega, Nat.cast_succ, hz, Int.floor_intCast]`. Conclude with `Int.toNat_of_nonneg h0` after adjusting the coercions.
-/
theorem aMi_cast (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (p q c : ℕ) (hp : p = D.R.k + i) (hq : q = D.R.m - (i + 1))
    (hc : c < q) :
    (aMi D i p q τ (q - 1 - c) : ℚ) =
      -((D.hc τ).e i + Formalism.L2.NTheta.lamAt (D.hc τ) (p + c) + ((c : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2) := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have h3 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) c p (by simp only [Ranks.r]; omega)
  have hm : (i : ℕ) + 1 < D.R.m := by omega
  have hl : Formalism.L2.NTheta.lamAt (D.hc τ) p = -(D.hc τ).b ⟨i + 1, hm⟩ := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dif_neg (by omega), dif_pos (by omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  rw [hl] at h3
  have g := (D.hc τ).gap_eb i hm
  obtain ⟨z1, h1⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) (p + c)
  obtain ⟨z2, h2⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have ht : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  have hz : -((D.hc τ).e i + Formalism.L2.NTheta.lamAt (D.hc τ) (p + c) + ((c : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2) =
      ((-(z2 + z1 + (c + 1) + s) : ℤ) : ℚ) := by
    rw [h1, h2, ht]; push_cast; ring
  have h0 : (0 : ℤ) ≤ -(z2 + z1 + (c + 1) + s) := by
    have : (0 : ℚ) ≤ ((-(z2 + z1 + (c + 1) + s) : ℤ) : ℚ) := by rw [← hz]; linarith
    exact_mod_cast this
  unfold aMi
  rw [if_pos (by omega), show q - (q - 1 - c) = c + 1 by omega, show p + (c + 1) - 1 = p + c by omega, Nat.cast_succ, hz,
    Int.floor_intCast]
  exact_mod_cast Int.toNat_of_nonneg h0

/- English proof (translation)
Introduce `D T _ κ hl ha hκ i σ hσ e he k ρ τ hτ c`. Establish `hlab` using `(GlobalTheory.ConjReading.branch_of_pins T ha hl.pins σ ρ).1 hσ`. Establish `he'` using `he ρ`. Generalize the expression as in `lab σ ρ = s at hlab he' ⊢`. Establish `hrt : ∀ t, tauE D t (T.Q.H.rt : D.host.E) = T.Q.H.rt0` using `hl.pins.1.2.2.2`.

Establish `hne : ∀ s t, tauE D s ≠ conjEmb (tauE D t)` using `fun s t h => by`. Establish `h1` using `RingHom.congr_fun h (T.Q.H.rt : D.host.E)`. Express the relevant statement in the definitionally equal form `_ = starRingEnd ℂ (tauE D t _) at h1`. Rewrite `h1` using `[hrt, hrt]`. Conclude with `conj_cmHostRoot_ne_self h1.symm`.

Establish `hrel : relab T.Q.c (res T σ) (tauE D s) = τ.1`. Rewrite using `[hτ, ← hlab]`. Use extensionality with `x`. Use `show σ (algebraMap T.Q.c.F D.what₂.LL (embF T.Q.c (tauE D s) x)) = σ (labLL D s x)`. Use `congr 1`.

Apply `D.what₂.embLL.injective` to reduce the goal to its premises. Establish `h1` using `RingHom.congr_fun (res_embLL T ha hl.pins.2.2.1) (embF T.Q.c (tauE D s) x)`. Establish `h2` using `RingHom.congr_fun D.embE_φ₀ ((D.host.sigmaOf (D.eTau s).1 : D.host.E →+* D.host.E) x)`. Conclude with `h1.trans h2.symm`. Establish `hi1 : Function.invFun (relab T.Q.c (res T σ)) τ.1 = tauE D s`.

Rewrite using `[← hrel]`. Conclude with `Function.leftInverse_invFun (relab_inj _ _) _`. Establish `hi2 : Function.invFun (relab T.Q.c (res T σ)) (conjEmb τ.1) = conjEmb (tauE D s)`. Rewrite using `[← hrel, ← relab_conjEmb]`. Conclude with `Function.leftInverse_invFun (relab_inj _ _) _`.

Establish `hp0 : ((T.U ((i : ℕ) + 1) (res T σ)).X k).p0 = (D.R.sigW ((i : ℕ) + 1)).2` using `((hl.unf _ (inR i) _ hσ).2.1 k).1.trans (hl.pins.2.2.2 _ (inR i)).2.1`. Establish `hs : (Wc D i).sig (tauE D s) = D.R.sigW ((i : ℕ) + 1)` using `D.sp.W_sigval _ (inR i).1 (inR i).2 _`. Take `⟨hP, hM, hn⟩` from `hκ i s`. Rewrite `hP`, `hM` using `[hs]`. Establish `hi` using `i.2`.

Establish `hc` using `c.2`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i` using `by simp only [Ranks.sigW]; omega`. Establish `hq : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - (i + 1)` using `rfl`. Establish `hr : D.R.r = (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2`.

Rewrite using `[hp, hq]`. Simplify using `only [Ranks.r]`. Use linear arithmetic over natural numbers and integers. Take `⟨N, hN⟩` from `(κ i).n_even`. Establish `hN2 : (κ i).n / 2 = N` using `by omega`.

Establish `hNq : (N : ℚ) + N = ((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) + (D.R.sigW ((i : ℕ) + 1)).2 + D.R.t`. Establish `: N + N = (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 + D.R.t`. Rewrite using `[← hN, hn, ← hr]`. Both sides reduce to the same expression. Conclude with `this` after adjusting the coercions.

Unfold `laU wtCol`. Rewrite using `[hi1, hi2, hp0, hN2, wtA_pos hne, wtA_neg hne, ← sub_eq_iff_eq_add, eq_comm, Int.floor_eq_iff]`. Distinguish the cases in `h : (c : ℕ) < (D.R.sigW ((i : ℕ) + 1)).2`. Establish `h1 : (D.R.sigW ((i : ℕ) + 1)).2 - 1 - c < (D.R.sigW ((i : ℕ) + 1)).2` using `by omega`. Establish `h2` using `aMi_cast D i s _ _ c hp hq h`.

Rewrite using `[if_pos h, if_neg (not_le.2 h), ext0, dif_pos h1, hM]`. Use `push_cast`. Rewrite using `[h2, he']`. Apply the tactic sequence `constructor <;> linarith`. Establish `h1 : (c : ℕ) - (D.R.sigW ((i : ℕ) + 1)).2 < (D.R.sigW ((i : ℕ) + 1)).1` using `by omega`.

Establish `h2` using `aPl_cast D i s _ _ hp h1`. Rewrite using `[if_neg h, if_pos (not_lt.1 h), ext0, dif_pos h1, hP]`. Simplify using `only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one]`. Rewrite using `[h2, he']`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem laU_eq_wtCol : ∀ (D : D7) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → AlgTie T → KapIs κ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ (e : D.what₂.Tau → ℤ), (∀ ρ, (e ρ : ℚ) = (D.hc (lab σ ρ)).e i) → ∀ k (ρ : D.what₂.Tau) (τ : ((T.U ((i : ℕ) + 1) (res T σ)).X k).Ψ), τ.1 = tauE D ρ → ∀ c : Fin D.R.r, laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n k τ c = wtCol (D.hc (lab σ ρ)) (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 c + e ρ := by
  intro D T _ κ hl ha hκ i σ hσ e he k ρ τ hτ c
  have hlab := (GlobalTheory.ConjReading.branch_of_pins T ha hl.pins σ ρ).1 hσ
  have he' := he ρ
  generalize lab σ ρ = s at hlab he' ⊢
  have hrt : ∀ t, tauE D t (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hl.pins.1.2.2.2
  have hne : ∀ s t, tauE D s ≠ conjEmb (tauE D t) := fun s t h => by
    have h1 := RingHom.congr_fun h (T.Q.H.rt : D.host.E)
    change _ = starRingEnd ℂ (tauE D t _) at h1
    rw [hrt, hrt] at h1
    exact conj_cmHostRoot_ne_self h1.symm
  have hrel : relab T.Q.c (res T σ) (tauE D s) = τ.1 := by
    rw [hτ, ← hlab]
    ext x
    show σ (algebraMap T.Q.c.F D.what₂.LL (embF T.Q.c (tauE D s) x)) = σ (labLL D s x)
    congr 1
    apply D.what₂.embLL.injective
    have h1 := RingHom.congr_fun (res_embLL T ha hl.pins.2.2.1) (embF T.Q.c (tauE D s) x)
    have h2 := RingHom.congr_fun D.embE_φ₀ ((D.host.sigmaOf (D.eTau s).1 : D.host.E →+* D.host.E) x)
    exact h1.trans h2.symm
  have hi1 : Function.invFun (relab T.Q.c (res T σ)) τ.1 = tauE D s := by
    rw [← hrel]; exact Function.leftInverse_invFun (relab_inj _ _) _
  have hi2 : Function.invFun (relab T.Q.c (res T σ)) (conjEmb τ.1) = conjEmb (tauE D s) := by
    rw [← hrel, ← relab_conjEmb]; exact Function.leftInverse_invFun (relab_inj _ _) _
  have hp0 : ((T.U ((i : ℕ) + 1) (res T σ)).X k).p0 = (D.R.sigW ((i : ℕ) + 1)).2 :=
    ((hl.unf _ (inR i) _ hσ).2.1 k).1.trans (hl.pins.2.2.2 _ (inR i)).2.1
  have hs : (Wc D i).sig (tauE D s) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
  obtain ⟨hP, hM, hn⟩ := hκ i s
  rw [hs] at hP hM
  have hi := i.2
  have hc := c.2
  have hk := D.R.m_add_three_le_k
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by simp only [Ranks.sigW]; omega
  have hq : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - (i + 1) := rfl
  have hr : D.R.r = (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 := by
    rw [hp, hq]; simp only [Ranks.r]; omega
  obtain ⟨N, hN⟩ := (κ i).n_even
  have hN2 : (κ i).n / 2 = N := by omega
  have hNq : (N : ℚ) + N = ((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) + (D.R.sigW ((i : ℕ) + 1)).2 + D.R.t := by
    have : N + N = (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 + D.R.t := by
      rw [← hN, hn, ← hr]; rfl
    exact_mod_cast this
  unfold laU wtCol
  rw [hi1, hi2, hp0, hN2, wtA_pos hne, wtA_neg hne, ← sub_eq_iff_eq_add, eq_comm, Int.floor_eq_iff]
  by_cases h : (c : ℕ) < (D.R.sigW ((i : ℕ) + 1)).2
  · have h1 : (D.R.sigW ((i : ℕ) + 1)).2 - 1 - c < (D.R.sigW ((i : ℕ) + 1)).2 := by omega
    have h2 := aMi_cast D i s _ _ c hp hq h
    rw [if_pos h, if_neg (not_le.2 h), ext0, dif_pos h1, hM]
    push_cast
    rw [h2, he']
    constructor <;> linarith
  · have h1 : (c : ℕ) - (D.R.sigW ((i : ℕ) + 1)).2 < (D.R.sigW ((i : ℕ) + 1)).1 := by omega
    have h2 := aPl_cast D i s _ _ hp h1
    rw [if_neg h, if_pos (not_lt.1 h), ext0, dif_pos h1, hP]
    simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [h2, he']
    constructor <;> linarith

end GlobalTheory.HolRead.SecWt
