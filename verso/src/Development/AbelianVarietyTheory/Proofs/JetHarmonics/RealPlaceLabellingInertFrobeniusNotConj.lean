import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.InertLabelling

open GlobalTheory.LevelsOrbits

/- English proof (translation)
Unfold `NumDatum.pos at h`. Establish `h1` using `congrArg Prod.fst h`. Establish `h2` using `congrArg Prod.snd h`. Simplify using `only at h1 h2`. Establish `h3 : u • N.hP l = 0` using `by simpa using h2`.

Unfold `NumDatum.ordP`. Distinguish the cases in `hc : N.cls l = PrimeClass.signal`. Rewrite using `[if_pos hc]`. Establish `ho : ¬ Odd u`. Introduce `ho`.

Rewrite `h1` using `[decide_eq_true (⟨hc, ho⟩ : N.cls l = PrimeClass.signal ∧ Odd u)]`. Apply the tactic sequence `cases hz : z.1 <;> simp [hz] at h1`. Take `⟨t, rfl⟩` from `Nat.not_odd_iff_even.1 ho`. Rewrite using `[← two_mul]`. Use `Nat.mul_dvd_mul_left 2 (addOrderOf_dvd_of_nsmul_eq_zero ?_)` and prove the remaining obligations.

Rewrite using `[← mul_smul, mul_two, h3]`. Rewrite using `[if_neg hc]`. Conclude with `addOrderOf_dvd_of_nsmul_eq_zero h3`.
-/
lemma ordP_dvd_of_pos_eq (N : NumDatum) (l : ℕ) (z : RPl N.R) (u : ℕ) (h : N.pos l z u = z) : N.ordP l ∣ u := by
  unfold NumDatum.pos at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp only at h1 h2
  have h3 : u • N.hP l = 0 := by simpa using h2
  unfold NumDatum.ordP
  by_cases hc : N.cls l = PrimeClass.signal
  · rw [if_pos hc]
    have ho : ¬ Odd u := by
      intro ho
      rw [decide_eq_true (⟨hc, ho⟩ : N.cls l = PrimeClass.signal ∧ Odd u)] at h1
      cases hz : z.1 <;> simp [hz] at h1
    obtain ⟨t, rfl⟩ := Nat.not_odd_iff_even.1 ho
    rw [← two_mul]
    refine Nat.mul_dvd_mul_left 2 (addOrderOf_dvd_of_nsmul_eq_zero ?_)
    rw [← mul_smul, mul_two, h3]
  · rw [if_neg hc]
    exact addOrderOf_dvd_of_nsmul_eq_zero h3

/- English proof (translation)
Use `wlog hst : s.val ≤ t.val generalizing s t`. Conclude with `(this t s h.symm (not_le.1 hst).le).symm`. Take `⟨u, hu⟩` from `Nat.exists_eq_add_of_le hst`. Rewrite `h` using `[hu, ← pos_add]`. Establish `hd` using `ordP_dvd_of_pos_eq N l _ u h.symm`.

Establish `hlt` using `ZMod.val_lt t`. Establish `: u = 0` using `Nat.eq_zero_of_dvd_of_lt hd (by omega)`. Apply `ZMod.val_injective` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.
-/
lemma pos_inj (N : NumDatum) (l : ℕ) (z : RPl N.R) (s t : ZMod (N.ordP l))
    (h : N.pos l z s.val = N.pos l z t.val) : s = t := by
  wlog hst : s.val ≤ t.val generalizing s t
  · exact (this t s h.symm (not_le.1 hst).le).symm
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hst
  rw [hu, ← pos_add] at h
  have hd := ordP_dvd_of_pos_eq N l _ u h.symm
  have hlt := ZMod.val_lt t
  have : u = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  apply ZMod.val_injective
  omega

def orbSetoid (N : NumDatum) (l : ℕ) : Setoid (RPl N.R) where
  r z z' := ∃ s : ℕ, N.pos l z s = z'
  iseqv := ⟨fun z => ⟨N.ordP l * 0, pos_mul_period N l z 0⟩, fun {z z'} ⟨s, hs⟩ => ⟨(N.ordP l - 1) * s, by
      have hp : 0 < N.ordP l := Nat.pos_of_ne_zero (NeZero.ne _)
      obtain ⟨n, hn⟩ : ∃ n, N.ordP l = n + 1 := ⟨N.ordP l - 1, by omega⟩
      rw [← hs, pos_add, show s + (N.ordP l - 1) * s = N.ordP l * s by rw [hn, Nat.add_sub_cancel]; ring,
        pos_mul_period]⟩,
    fun {a b c} ⟨s, hs⟩ ⟨t, ht⟩ => ⟨s + t, by rw [← pos_add, hs, ht]⟩⟩

/- English proof (translation)
Use `⟨Finset.univ.filter fun z => (Quotient.mk (orbSetoid N l) z).out = z, fun z' => ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩ : (orbSetoid N l).r (Quotient.mk (orbSetoid N l) z').out z'` from `Quotient.mk_out z'`. Establish `key : ∀ p : RPl N.R × ZMod (N.ordP l), p.1 ∈ (Finset.univ.filter fun z => (Quotient.mk (orbSetoid N l) z).out = z) ∧ N.pos l p.1 p.2.val = z' → p.1 = (Quotient.mk (orbSetoid N l) z').out`. Introduce and unpack `p ⟨h1, h2⟩`. Rewrite using `[← (Finset.mem_filter.1 h1).2]`.

Use `congr 1`. Conclude with `Quotient.sound ⟨_, h2⟩`. Use `⟨((Quotient.mk (orbSetoid N l) z').out, (s : ZMod (N.ordP l))), ⟨?_, ?_⟩, fun p hp => ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[ZMod.val_natCast, pos_mod, hs]`.

Establish `h1` using `key p hp`. Use `Prod.ext h1 (pos_inj N l p.1 _ _ ?_)` and prove the remaining obligations. Rewrite using `[hp.2, ZMod.val_natCast, pos_mod, h1, hs]`.
-/
lemma exists_reps (N : NumDatum) (l : ℕ) : ∃ Z : Finset (RPl N.R),
    ∀ z' : RPl N.R, ∃! p : RPl N.R × ZMod (N.ordP l), p.1 ∈ Z ∧ N.pos l p.1 p.2.val = z' := by
  refine ⟨Finset.univ.filter fun z => (Quotient.mk (orbSetoid N l) z).out = z, fun z' => ?_⟩
  obtain ⟨s, hs⟩ : (orbSetoid N l).r (Quotient.mk (orbSetoid N l) z').out z' := Quotient.mk_out z'
  have key : ∀ p : RPl N.R × ZMod (N.ordP l),
      p.1 ∈ (Finset.univ.filter fun z => (Quotient.mk (orbSetoid N l) z).out = z) ∧ N.pos l p.1 p.2.val = z' →
      p.1 = (Quotient.mk (orbSetoid N l) z').out := by
    rintro p ⟨h1, h2⟩
    rw [← (Finset.mem_filter.1 h1).2]
    congr 1
    exact Quotient.sound ⟨_, h2⟩
  refine ⟨((Quotient.mk (orbSetoid N l) z').out, (s : ZMod (N.ordP l))), ⟨?_, ?_⟩, fun p hp => ?_⟩
  · simp
  · rw [ZMod.val_natCast, pos_mod, hs]
  · have h1 := key p hp
    refine Prod.ext h1 (pos_inj N l p.1 _ _ ?_)
    rw [hp.2, ZMod.val_natCast, pos_mod, h1, hs]

/- English proof (translation)
The claim follows from `GlobalTheory.GoodDepth.even_ordP_of_not_conjIn hI hC`.
-/
lemma even_ordP (N : NumDatum) (l : ℕ) (hI : Inert N l) (hC : ¬ ConjIn N l) : Even (N.ordP l) :=
  GlobalTheory.GoodDepth.even_ordP_of_not_conjIn hI hC

/- English proof (translation)
Establish `h : Even (s + 1).val ↔ ¬ Even s.val`. Establish `e : s + 1 = ((s.val + 1 : ℕ) : ZMod d)` using `by simp`. Rewrite using `[e, ZMod.val_natCast, ← Nat.even_add_one, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ (even_iff_two_dvd.1 hd)]`. Unfold `RF.bg`. Distinguish the cases in `hs : Even s.val`.

Apply the tactic sequence `rw [if_pos hs, if_neg (fun hh => h.1 hh hs)]; fin_cases g <;> simp`. Apply the tactic sequence `rw [if_neg hs, if_pos (h.2 hs)]; fin_cases g <;> simp`.
-/
lemma bg_succ {d : ℕ} [NeZero d] (hd : Even d) (s : ZMod d) (g : Fin 2) : g = RF.bg (s + 1) ↔ ¬ g = RF.bg s := by
  have h : Even (s + 1).val ↔ ¬ Even s.val := by
    have e : s + 1 = ((s.val + 1 : ℕ) : ZMod d) := by simp
    rw [e, ZMod.val_natCast, ← Nat.even_add_one, Nat.even_iff, Nat.even_iff,
      Nat.mod_mod_of_dvd _ (even_iff_two_dvd.1 hd)]
  unfold RF.bg
  by_cases hs : Even s.val
  · rw [if_pos hs, if_neg (fun hh => h.1 hh hs)]; fin_cases g <;> simp
  · rw [if_neg hs, if_pos (h.2 hs)]; fin_cases g <;> simp

/- English proof (translation)
Establish `e : s + 1 = ((s.val + 1 : ℕ) : ZMod (N.ordP l))` using `by simp`. Rewrite using `[e, ZMod.val_natCast, pos_mod, pos_add]`.
-/
lemma pos_succ (N : NumDatum) (l : ℕ) (z : RPl N.R) (s : ZMod (N.ordP l)) :
    N.pos l z (s + 1).val = N.pos l (N.pos l z s.val) 1 := by
  have e : s + 1 = ((s.val + 1 : ℕ) : ZMod (N.ordP l)) := by simp
  rw [e, ZMod.val_natCast, pos_mod, pos_add]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

/- English proof (translation)
Establish `hd : (H.d : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 H.d_prime.ne_zero`. Establish `h0 : H.rt0 ≠ 0` using `fun h => by`. Use `H.sqrt_neg_disc_sq` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `hd (by linear_combination this)`.

Establish `h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ)`. Establish `: ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E)`. Use `congrArg (algebraMap (𝓞 E) E) H.rt_sq` as an intermediate fact. Simplify using `using this`. Rewrite using `[← map_pow, this, map_neg, map_natCast]`.

Establish `h2 : ∀ w : ℂ, w ^ 2 = -(H.d : ℂ) → starRingEnd ℂ w = -w`. Introduce `w hw`. Establish `hre` using `congrArg Complex.re hw`. Establish `him` using `congrArg Complex.im hw`. Simplify using `[pow_two] at hre him`.

Establish `hdp : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `: w.re = 0`. Assume the negation of the conclusion as `hne`. Establish `: w.im = 0`. Establish `: w.re * w.im = 0` using `by linarith`.

Conclude with `(mul_eq_zero.1 this).resolve_left hne`. Rewrite `hre` using `[this]`. Use polynomial arithmetic with `[mul_self_nonneg w.re]`. Apply the tactic sequence `apply Complex.ext <;> simp [this]`. Unfold `InPsi`.

Rewrite using `[ComplexEmbedding.conjugate_coe_eq, h2 _ h1]`. Establish `h3 : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0` using `sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm)`. Prove the components needed by the constructor for the conclusion. Introduce `a b`. Conclude with `h0 (by linear_combination (-1/2 : ℂ) * a - (1/2 : ℂ) * b)`.

Introduce `a`. Rewrite using `[h3.resolve_left a, neg_neg]`.
-/
lemma inPsi_conj_iff (τ : E →+* ℂ) : InPsi H (ComplexEmbedding.conjugate τ) ↔ ¬ InPsi H τ := by
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have h0 : H.rt0 ≠ 0 := fun h => by
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    exact hd (by linear_combination this)
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [← map_pow, this, map_neg, map_natCast]
  have h2 : ∀ w : ℂ, w ^ 2 = -(H.d : ℂ) → starRingEnd ℂ w = -w := by
    intro w hw
    have hre := congrArg Complex.re hw
    have him := congrArg Complex.im hw
    simp [pow_two] at hre him
    have hdp : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have : w.re = 0 := by
      by_contra hne
      have : w.im = 0 := by
        have : w.re * w.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg w.re]
    apply Complex.ext <;> simp [this]
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq, h2 _ h1]
  have h3 : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm)
  constructor
  · intro a b
    exact h0 (by linear_combination (-1/2 : ℂ) * a - (1/2 : ℂ) * b)
  · intro a
    rw [h3.resolve_left a, neg_neg]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[embK_coe, embK_coe, H.bar_eq, IsCMField.complexEmbedding_complexConj]`. Both sides reduce to the same expression.
-/
lemma embK_conj_bar {lv : Level H} (c : Coeff lv) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c τ (H.bar x) = embK c (ComplexEmbedding.conjugate τ) x := by
  apply Subtype.ext
  rw [embK_coe, embK_coe, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

/- English proof (translation)
The claim follows from `ComplexEmbedding.involutive_conjugate E τ`.
-/
lemma conj_conj (τ : E →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
  ComplexEmbedding.involutive_conjugate E τ

/- English proof (translation)
Introduce `E _ _ _ H lv c N pl hT la T io C _ _ V ι _ hl hla hI hC j`. Take `⟨Z, hZ⟩` from `exists_reps N V.l`. Establish `hev` using `even_ordP N V.l hI hC`. Establish `hin : ∀ z, InPsi H (pl z)` using `fun z => (hT.psi _).2 ⟨z, rfl⟩`. Establish `hne : ∀ z z', pl z ≠ ComplexEmbedding.conjugate (pl z')` using `fun z z' h => (inPsi_conj_iff (pl z')).1 (h ▸ hin z) (hin z')`.

Establish `hcinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ))` using `(ComplexEmbedding.involutive_conjugate E).injective`. Use `⟨Z, hZ, ?_, hev, ⟨?_, ?_⟩, fun z g => ⟨fun s x => ?_, fun s => ?_⟩⟩` and prove the remaining obligations. Take `⟨p, hp, -⟩` from `hZ (false, 0)`. Conclude with `⟨p.1, hp.1⟩`. Introduce and unpack `⟨z, g, s⟩ ⟨z', g', s'⟩ h`.

Establish `main : N.pos V.l z.1 s.val = N.pos V.l z'.1 s'.val → (g = RF.bg s ↔ g' = RF.bg s') → (z, g, s) = (z', g', s')`. Introduce `h1 h2`. Use `(hZ _).unique (y₁ := (z.1, s)) (y₂ := (z'.1, s')) ⟨z.2, h1⟩ ⟨z'.2, rfl⟩` as an intermediate fact. Take `⟨a, b⟩` from `Prod.mk.inj this`. Take `rfl` from `Subtype.ext a`.

Substitute `b` using the available equality. Establish `: g = g'` using `(by decide : ∀ g g' b : Fin 2, (g = b ↔ g' = b) → g = g') _ _ _ h2`. Rewrite using `[this]`. Simplify using `only [tauIn] at h`. Apply the tactic sequence `by_cases a : g = RF.bg s <;> by_cases b : g' = RF.bg s'`.

Rewrite `h` using `[if_pos a, if_pos b]`. Conclude with `main (hT.inj h) (by tauto)`. Rewrite `h` using `[if_pos a, if_neg b]`. Conclude with `absurd h (hne _ _)`. Rewrite `h` using `[if_neg a, if_pos b]`.

Conclude with `absurd h.symm (hne _ _)`. Rewrite `h` using `[if_neg a, if_neg b]`. Conclude with `main (hT.inj (hcinj h)) (by tauto)`. Introduce `τ`. Distinguish the cases in `h : InPsi H τ`.

Take `⟨z', rfl⟩` from `(hT.psi _).1 h`. Take `⟨p, hp, -⟩` from `hZ z'`. Use `⟨(⟨p.1, hp.1⟩, RF.bg p.2, p.2), ?_⟩` and prove the remaining obligations. Simplify using `only [tauIn]`. Rewrite using `[if_pos rfl, hp.2]`.

Take `⟨z', hz'⟩` from `(hT.psi _).1 ((inPsi_conj_iff τ).2 h)`. Take `⟨p, hp, -⟩` from `hZ z'`. Use `⟨(⟨p.1, hp.1⟩, RF.bg (p.2 + 1), p.2), ?_⟩` and prove the remaining obligations. Simplify using `only [tauIn]`. Rewrite using `[if_neg ((bg_succ hev _ _).1 rfl), hp.2, hz', conj_conj]`.

Establish `hf : ∀ (w : RPl N.R) (x : 𝓞 E), V.MM (emA3 io ι (ComplexEmbedding.conjugate (pl (N.pos V.l w 1))) x - emA3 io ι (pl w) x ^ V.l)`. Introduce `w x`. Take `⟨y, hy, e⟩` from `hT.frob la (hl ▸ hI) w x`. Use `hla y hy` as an intermediate fact. Rewrite `this` using `[e, ← hl, map_sub, map_sub, map_pow, map_pow]`.

Conclude with `this`. Unfold `tauIn`. Rewrite using `[pos_succ]`. Distinguish the cases in `a : g = RF.bg s`. Rewrite using `[if_pos a, if_neg (fun hh => (bg_succ hev _ _).1 hh a)]`.

Conclude with `hf _ _`. Rewrite using `[if_neg a, if_pos ((bg_succ hev _ _).2 a)]`. Use `hf (N.pos V.l z s.val) (H.bar x)` as an intermediate fact. Simplify using `only [emA3, RingHom.comp_apply, embK_conj_bar, conj_conj] at this ⊢`. Conclude with `this`.

Unfold `tauIn`. Distinguish the cases in `a : (0 : Fin 2) = RF.bg s`. Rewrite using `[if_pos a, if_neg (by rw [← a]; decide)]`. Rewrite using `[if_neg a, if_pos (by revert a; generalize RF.bg s = b; revert b; decide), conj_conj]`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → V.l = resCharOf la → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) → Inert N V.l → ¬ ConjIn N V.l → ∀ j : ℕ, ∃ Z : Finset (RPl N.R), RF.IsReps (parOf N j V.l) Z ∧ Z.Nonempty ∧ Even (N.ordP V.l) ∧ Function.Bijective (fun x : Z × Fin 2 × ZMod (N.ordP V.l) => tauIn N pl V.l x.1.1 x.2.1 x.2.2) ∧ ∀ z g, FrobOrd V io ι (tauIn N pl V.l z g) ∧ ∀ s, tauIn N pl V.l z 1 s = ComplexEmbedding.conjugate (tauIn N pl V.l z 0 s) := by
  intro E _ _ _ H lv c N pl hT la T io C _ _ V ι _ hl hla hI hC j
  obtain ⟨Z, hZ⟩ := exists_reps N V.l
  have hev := even_ordP N V.l hI hC
  have hin : ∀ z, InPsi H (pl z) := fun z => (hT.psi _).2 ⟨z, rfl⟩
  have hne : ∀ z z', pl z ≠ ComplexEmbedding.conjugate (pl z') := fun z z' h =>
    (inPsi_conj_iff (pl z')).1 (h ▸ hin z) (hin z')
  have hcinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
    (ComplexEmbedding.involutive_conjugate E).injective
  refine ⟨Z, hZ, ?_, hev, ⟨?_, ?_⟩, fun z g => ⟨fun s x => ?_, fun s => ?_⟩⟩
  · obtain ⟨p, hp, -⟩ := hZ (false, 0)
    exact ⟨p.1, hp.1⟩
  · rintro ⟨z, g, s⟩ ⟨z', g', s'⟩ h
    have main : N.pos V.l z.1 s.val = N.pos V.l z'.1 s'.val → (g = RF.bg s ↔ g' = RF.bg s') →
        (z, g, s) = (z', g', s') := by
      intro h1 h2
      have := (hZ _).unique (y₁ := (z.1, s)) (y₂ := (z'.1, s')) ⟨z.2, h1⟩ ⟨z'.2, rfl⟩
      obtain ⟨a, b⟩ := Prod.mk.inj this
      obtain rfl := Subtype.ext a
      subst b
      have : g = g' := (by decide : ∀ g g' b : Fin 2, (g = b ↔ g' = b) → g = g') _ _ _ h2
      rw [this]
    dsimp only [tauIn] at h
    by_cases a : g = RF.bg s <;> by_cases b : g' = RF.bg s'
    · rw [if_pos a, if_pos b] at h
      exact main (hT.inj h) (by tauto)
    · rw [if_pos a, if_neg b] at h
      exact absurd h (hne _ _)
    · rw [if_neg a, if_pos b] at h
      exact absurd h.symm (hne _ _)
    · rw [if_neg a, if_neg b] at h
      exact main (hT.inj (hcinj h)) (by tauto)
  · intro τ
    by_cases h : InPsi H τ
    · obtain ⟨z', rfl⟩ := (hT.psi _).1 h
      obtain ⟨p, hp, -⟩ := hZ z'
      refine ⟨(⟨p.1, hp.1⟩, RF.bg p.2, p.2), ?_⟩
      dsimp only [tauIn]
      rw [if_pos rfl, hp.2]
    · obtain ⟨z', hz'⟩ := (hT.psi _).1 ((inPsi_conj_iff τ).2 h)
      obtain ⟨p, hp, -⟩ := hZ z'
      refine ⟨(⟨p.1, hp.1⟩, RF.bg (p.2 + 1), p.2), ?_⟩
      dsimp only [tauIn]
      rw [if_neg ((bg_succ hev _ _).1 rfl), hp.2, hz', conj_conj]
  · have hf : ∀ (w : RPl N.R) (x : 𝓞 E), V.MM (emA3 io ι (ComplexEmbedding.conjugate (pl (N.pos V.l w 1))) x -
        emA3 io ι (pl w) x ^ V.l) := by
      intro w x
      obtain ⟨y, hy, e⟩ := hT.frob la (hl ▸ hI) w x
      have := hla y hy
      rw [e, ← hl, map_sub, map_sub, map_pow, map_pow] at this
      exact this
    unfold tauIn
    rw [pos_succ]
    by_cases a : g = RF.bg s
    · rw [if_pos a, if_neg (fun hh => (bg_succ hev _ _).1 hh a)]
      exact hf _ _
    · rw [if_neg a, if_pos ((bg_succ hev _ _).2 a)]
      have := hf (N.pos V.l z s.val) (H.bar x)
      simp only [emA3, RingHom.comp_apply, embK_conj_bar, conj_conj] at this ⊢
      exact this
  · unfold tauIn
    by_cases a : (0 : Fin 2) = RF.bg s
    · rw [if_pos a, if_neg (by rw [← a]; decide)]
    · rw [if_neg a, if_pos (by revert a; generalize RF.bg s = b; revert b; decide), conj_conj]

end GlobalTheory.InertLabelling
