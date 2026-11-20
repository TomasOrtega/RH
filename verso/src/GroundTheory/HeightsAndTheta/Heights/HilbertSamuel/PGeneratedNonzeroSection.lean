import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedNonzeroSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedNonzeroSection

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

section Faces

variable {S : Type} [CommRing S]

/- English proof (translation)
Establish `hne : ∀ k, (I.1 k).Nonempty` using `I.2.1`. Establish `hcard₀ : (I.1 k₀).card = 2` using `by rw [hI]; exact Finset.card_pair hab`. Establish `hface : ∀ i ∈ I.1 k₀, (∀ l, (Function.update I.1 k₀ ((I.1 k₀).erase i) l).Nonempty) ∧ ∑ l, ((Function.update I.1 k₀ ((I.1 k₀).erase i) l).card - 1) = 0`. Introduce `i hi`. Establish `hc : ((I.1 k₀).erase i).card = 1` using `by rw [Finset.card_erase_of_mem hi, hcard₀]`.

Use `⟨fun l => ?_, Finset.sum_eq_zero fun l _ => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hl : l = k₀`. Substitute `hl; rw [Function.update_self]; exact Finset.card_pos.mp (by omega)` using the available equality. Rewrite using `[Function.update_of_ne hl]`. Conclude with `hne l`.

Distinguish the cases in `hl : l = k₀`. Substitute `hl` using the available equality. Rewrite using `[Function.update_self, hc]`. Both sides reduce to the same expression. Rewrite using `[Function.update_of_ne hl, hother l hl]`.

Both sides reduce to the same expression. Establish `ha : a ∈ I.1 k₀` using `by rw [hI]; simp`. Establish `hb : b ∈ I.1 k₀` using `by rw [hI]; simp`. Take `rfl : J₁ = ⟨_, hface a ha⟩` from `Subtype.ext h₁`. Take `rfl : J₂ = ⟨_, hface b hb⟩` from `Subtype.ext h₂`.

Establish `hsign : KH.faceSign I.1 k₀ b = -KH.faceSign I.1 k₀ a`. Unfold `KH.faceSign`. Break down `lt_or_gt_of_ne hab with h | h` into its components or cases. Establish `e₁ : ((I.1 k₀).filter (· < a)).card = 0`. Rewrite using `[hI]`.

Simplify using `[Finset.filter_insert, Finset.filter_singleton, h.not_gt]`. Establish `e₂ : ((I.1 k₀).filter (· < b)).card = 1`. Rewrite using `[hI]`. Simplify using `[Finset.filter_insert, Finset.filter_singleton, h]`. Rewrite using `[e₁, e₂, add_comm 1, pow_succ, zero_add]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e₁ : ((I.1 k₀).filter (· < a)).card = 1`. Rewrite using `[hI]`. Simplify using `[Finset.filter_insert, Finset.filter_singleton, h]`. Establish `e₂ : ((I.1 k₀).filter (· < b)).card = 0`.

Rewrite using `[hI]`. Simplify using `[Finset.filter_insert, Finset.filter_singleton, h.not_gt]`. Rewrite using `[e₁, e₂, add_comm 1, pow_succ, zero_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : KH.faceSign I.1 k₀ a = 1 ∨ KH.faceSign I.1 k₀ a = -1`.

Unfold `KH.faceSign`. Conclude with `neg_one_pow_eq_or ℤ _`. Establish `hd : KH.cechD S ι M 0 f I = KH.faceSign I.1 k₀ a • (KH.cellRes S M _ I.1 (f ⟨_, hface a ha⟩) - KH.cellRes S M _ I.1 (f ⟨_, hface b hb⟩))`. Express the relevant statement in the definitionally equal form `(∑ k : K, ∑ i ∈ I.1 k, _ : KH.CechC S ι M 0 →ₗ[MRingOver S ι] LocalizedModule (KH.cellMon S I.1) M) f = _`. Rewrite using `[Finset.sum_eq_single k₀, Finset.sum_eq_add_of_mem a b ha hb hab, dif_pos (hface a ha), dif_pos (hface b hb)]`.

Rewrite using `[hsign, LinearMap.add_apply]`. Express the relevant statement in the definitionally equal form `KH.faceSign I.1 k₀ a • (KH.cellRes S M _ I.1 (f _)) + (-KH.faceSign I.1 k₀ a) • (KH.cellRes S M _ I.1 (f _)) = _`. Rewrite using `[neg_smul, ← sub_eq_add_neg]`. Conclude with `(zsmul_sub _ _ _).symm`. Introduce `i hi hne'`.

Establish `: i = a ∨ i = b` using `by rw [hI] at hi; simpa using hi`. The claim follows by propositional logic. Introduce `l _ hl`. Use `Finset.sum_eq_zero fun i hi => dif_neg fun h => ?_` and prove the remaining obligations. Use `(h.1 l)` as an intermediate fact.

Rewrite `this` using `[Function.update_self, ← Finset.card_pos, Finset.card_erase_of_mem hi, hother l hl]`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Conclude with `absurd (Finset.mem_univ k₀) h`. Conclude with `GenTwistGenerated.res_eq_of_cechD hs hd h0`.
-/
theorem res_eq_of_faces {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (I : KH.Cell K ι 1) (k₀ : K)
    {a b : ι k₀} (hab : a ≠ b) (hI : I.1 k₀ = {a, b}) (hother : ∀ l, l ≠ k₀ → (I.1 l).card = 1)
    (J₁ J₂ : KH.Cell K ι 0) (h₁ : J₁.1 = Function.update I.1 k₀ ((I.1 k₀).erase a))
    (h₂ : J₂.1 = Function.update I.1 k₀ ((I.1 k₀).erase b)) {f : KH.CechC S ι M 0}
    (h0 : KH.cechD S ι M 0 f = 0) :
    KH.cellRes S M J₁.1 I.1 (f J₁) = KH.cellRes S M J₂.1 I.1 (f J₂) := by
  classical
  have hne : ∀ k, (I.1 k).Nonempty := I.2.1
  have hcard₀ : (I.1 k₀).card = 2 := by rw [hI]; exact Finset.card_pair hab
  have hface : ∀ i ∈ I.1 k₀, (∀ l, (Function.update I.1 k₀ ((I.1 k₀).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update I.1 k₀ ((I.1 k₀).erase i) l).card - 1) = 0 := by
    intro i hi
    have hc : ((I.1 k₀).erase i).card = 1 := by rw [Finset.card_erase_of_mem hi, hcard₀]
    refine ⟨fun l => ?_, Finset.sum_eq_zero fun l _ => ?_⟩
    · by_cases hl : l = k₀
      · subst hl; rw [Function.update_self]; exact Finset.card_pos.mp (by omega)
      · rw [Function.update_of_ne hl]; exact hne l
    · by_cases hl : l = k₀
      · subst hl; rw [Function.update_self, hc]; rfl
      · rw [Function.update_of_ne hl, hother l hl]; rfl
  have ha : a ∈ I.1 k₀ := by rw [hI]; simp
  have hb : b ∈ I.1 k₀ := by rw [hI]; simp
  obtain rfl : J₁ = ⟨_, hface a ha⟩ := Subtype.ext h₁
  obtain rfl : J₂ = ⟨_, hface b hb⟩ := Subtype.ext h₂
  have hsign : KH.faceSign I.1 k₀ b = -KH.faceSign I.1 k₀ a := by
    unfold KH.faceSign
    rcases lt_or_gt_of_ne hab with h | h
    · have e₁ : ((I.1 k₀).filter (· < a)).card = 0 := by
        rw [hI]; simp [Finset.filter_insert, Finset.filter_singleton, h.not_gt]
      have e₂ : ((I.1 k₀).filter (· < b)).card = 1 := by
        rw [hI]; simp [Finset.filter_insert, Finset.filter_singleton, h]
      rw [e₁, e₂, add_comm 1, pow_succ, zero_add]; ring
    · have e₁ : ((I.1 k₀).filter (· < a)).card = 1 := by
        rw [hI]; simp [Finset.filter_insert, Finset.filter_singleton, h]
      have e₂ : ((I.1 k₀).filter (· < b)).card = 0 := by
        rw [hI]; simp [Finset.filter_insert, Finset.filter_singleton, h.not_gt]
      rw [e₁, e₂, add_comm 1, pow_succ, zero_add]; ring
  have hs : KH.faceSign I.1 k₀ a = 1 ∨ KH.faceSign I.1 k₀ a = -1 := by
    unfold KH.faceSign; exact neg_one_pow_eq_or ℤ _
  have hd : KH.cechD S ι M 0 f I = KH.faceSign I.1 k₀ a •
      (KH.cellRes S M _ I.1 (f ⟨_, hface a ha⟩) - KH.cellRes S M _ I.1 (f ⟨_, hface b hb⟩)) := by
    change (∑ k : K, ∑ i ∈ I.1 k, _ :
      KH.CechC S ι M 0 →ₗ[MRingOver S ι] LocalizedModule (KH.cellMon S I.1) M) f = _
    rw [Finset.sum_eq_single k₀, Finset.sum_eq_add_of_mem a b ha hb hab, dif_pos (hface a ha),
      dif_pos (hface b hb)]
    · rw [hsign, LinearMap.add_apply]
      change KH.faceSign I.1 k₀ a • (KH.cellRes S M _ I.1 (f _)) +
        (-KH.faceSign I.1 k₀ a) • (KH.cellRes S M _ I.1 (f _)) = _
      rw [neg_smul, ← sub_eq_add_neg]
      exact (zsmul_sub _ _ _).symm
    · intro i hi hne'
      have : i = a ∨ i = b := by rw [hI] at hi; simpa using hi
      tauto
    · intro l _ hl
      refine Finset.sum_eq_zero fun i hi => dif_neg fun h => ?_
      have := (h.1 l)
      rw [Function.update_self, ← Finset.card_pos, Finset.card_erase_of_mem hi, hother l hl] at this
      omega
    · intro h; exact absurd (Finset.mem_univ k₀) h
  exact GenTwistGenerated.res_eq_of_cechD hs hd h0

def chartCell (c : ∀ k, ι k) : KH.Cell K ι 0 :=
  ⟨fun k => {c k}, fun k => Finset.singleton_nonempty _, by simp⟩

/- English proof (translation)
Use `⟨fun k => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `Finset.insert_nonempty _ _`.

Rewrite using `[Function.update_of_ne hk]`. Conclude with `Finset.singleton_nonempty _`. Rewrite using `[Finset.sum_eq_single k₀]`. Rewrite using `[Function.update_self, Finset.card_pair hb.symm]`. Introduce `k _ hk`.

Rewrite using `[Function.update_of_ne hk, Finset.card_singleton]`. Both sides reduce to the same expression. Introduce `h`. Conclude with `absurd (Finset.mem_univ k₀) h`.
-/
theorem pairCell_prop (c : ∀ k, ι k) (k₀ : K) (b : ι k₀) (hb : b ≠ c k₀) :
    (∀ k, (Function.update (fun k => ({c k} : Finset (ι k))) k₀ {c k₀, b} k).Nonempty) ∧
      ∑ k, ((Function.update (fun k => ({c k} : Finset (ι k))) k₀ {c k₀, b} k).card - 1) = 1 := by
  classical
  refine ⟨fun k => ?_, ?_⟩
  · by_cases hk : k = k₀
    · subst hk; rw [Function.update_self]; exact Finset.insert_nonempty _ _
    · rw [Function.update_of_ne hk]; exact Finset.singleton_nonempty _
  · rw [Finset.sum_eq_single k₀]
    · rw [Function.update_self, Finset.card_pair hb.symm]
    · intro k _ hk
      rw [Function.update_of_ne hk, Finset.card_singleton]; rfl
    · intro h; exact absurd (Finset.mem_univ k₀) h

def pairCell (c : ∀ k, ι k) (k₀ : K) (b : ι k₀) (hb : b ≠ c k₀) : KH.Cell K ι 1 :=
  ⟨Function.update (fun k => ({c k} : Finset (ι k))) k₀ {c k₀, b}, pairCell_prop c k₀ b hb⟩

/- English proof (translation)
Use `(res_eq_of_faces (pairCell c k₀ b hb) k₀ hb.symm (by simp [pairCell]) (fun l hl => by simp only [pairCell]; rw [Function.update_of_ne hl, Finset.card_singleton]) (chartCell (Function.update c k₀ b)) (chartCell c) ?_ ?_ h0).symm` and prove the remaining obligations. Use function extensionality and compare the values at `l`. Distinguish the cases in `hl : l = k₀`. Substitute `hl` using the available equality. Simplify using `only [chartCell, pairCell, Function.update_self]`.

Use extensionality with `i`. Simplify using `only [Finset.mem_singleton, Finset.mem_erase, Finset.mem_insert]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `⟨hb, Or.inr rfl⟩`.

Introduce and unpack `⟨h1, h2 | h2⟩`. Conclude with `absurd h2 h1`. Conclude with `h2`. Simplify using `only [chartCell, pairCell, Function.update_of_ne hl]`. Use function extensionality and compare the values at `l`.

Distinguish the cases in `hl : l = k₀`. Substitute `hl` using the available equality. Simplify using `only [chartCell, pairCell, Function.update_self]`. Use extensionality with `i`. Simplify using `only [Finset.mem_singleton, Finset.mem_erase, Finset.mem_insert]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `⟨hb.symm, Or.inl rfl⟩`. Introduce and unpack `⟨h1, h2 | h2⟩`. Conclude with `h2`.

Conclude with `absurd h2 h1`. Simplify using `only [chartCell, pairCell, Function.update_of_ne hl]`.
-/
theorem res_eq_pair {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (c : ∀ k, ι k) (k₀ : K) (b : ι k₀)
    (hb : b ≠ c k₀) {f : KH.CechC S ι M 0} (h0 : KH.cechD S ι M 0 f = 0) :
    KH.cellRes S M (chartCell c).1 (pairCell c k₀ b hb).1 (f (chartCell c)) =
      KH.cellRes S M (chartCell (Function.update c k₀ b)).1 (pairCell c k₀ b hb).1
        (f (chartCell (Function.update c k₀ b))) := by
  classical
  refine (res_eq_of_faces (pairCell c k₀ b hb) k₀ hb.symm (by simp [pairCell])
    (fun l hl => by simp only [pairCell]; rw [Function.update_of_ne hl, Finset.card_singleton])
    (chartCell (Function.update c k₀ b)) (chartCell c) ?_ ?_ h0).symm
  · funext l
    by_cases hl : l = k₀
    · subst hl
      simp only [chartCell, pairCell, Function.update_self]
      ext i
      simp only [Finset.mem_singleton, Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro rfl; exact ⟨hb, Or.inr rfl⟩
      · rintro ⟨h1, h2 | h2⟩
        · exact absurd h2 h1
        · exact h2
    · simp only [chartCell, pairCell, Function.update_of_ne hl]
  · funext l
    by_cases hl : l = k₀
    · subst hl
      simp only [chartCell, pairCell, Function.update_self]
      ext i
      simp only [Finset.mem_singleton, Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro rfl; exact ⟨hb.symm, Or.inl rfl⟩
      · rintro ⟨h1, h2 | h2⟩
        · exact h2
        · exact absurd h2 h1
    · simp only [chartCell, pairCell, Function.update_of_ne hl]

end Faces

section Eval

variable {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω)

/- English proof (translation)
Establish `h : (MvPolynomial.eval (fun _ : K => (1 : Ω))).comp (mConeMap y : MRing ι →ₐ[ℤ] MvPolynomial K Ω).toRingHom = (aeval y : MRing ι →ₐ[ℤ] Ω).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using the standard rewrite rules. Introduce `p`.

Simplify using `[mConeMap]`. Establish `h2` using `RingHom.congr_fun h f`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2`. Rewrite using `[← h2, show mConeMap y f = 0 from (RingHom.mem_ker).mp hf, map_zero]`.
-/
theorem aeval_eq_zero_of_mem {f : MRing ι} (hf : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  have h : (MvPolynomial.eval (fun _ : K => (1 : Ω))).comp
      (mConeMap y : MRing ι →ₐ[ℤ] MvPolynomial K Ω).toRingHom = (aeval y : MRing ι →ₐ[ℤ] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro p; simp [mConeMap]
  have h2 := RingHom.congr_fun h f
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
  rw [← h2, show mConeMap y f = 0 from (RingHom.mem_ker).mp hf, map_zero]

/- English proof (translation)
The claim follows from `MvPolynomial.aeval_map_algebraMap ℚ y f`.
-/
theorem aeval_map_int (f : MRing ι) : aeval y (MvPolynomial.map (Int.castRingHom ℚ) f) = aeval y f :=
  MvPolynomial.aeval_map_algebraMap ℚ y f

/- English proof (translation)
Establish `hle : KH.genIdeal y ≤ RingHom.ker (aeval y : MRingOver ℚ ι →ₐ[ℚ] Ω)`. Unfold `KH.genIdeal`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `g hg`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, aeval_map_int]`.

Conclude with `aeval_eq_zero_of_mem y hg`. Conclude with `(RingHom.mem_ker).mp (hle hf)`.
-/
theorem aeval_eq_zero_of_mem_genIdeal (f : MRingOver ℚ ι) (hf : f ∈ KH.genIdeal y) : aeval y f = 0 := by
  have hle : KH.genIdeal y ≤ RingHom.ker (aeval y : MRingOver ℚ ι →ₐ[ℚ] Ω) := by
    unfold KH.genIdeal
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, aeval_map_int]
    exact aeval_eq_zero_of_mem y hg
  exact (RingHom.mem_ker).mp (hle hf)

def evQ : (MRingOver ℚ ι ⧸ KH.genIdeal y) →ₐ[ℚ] Ω :=
  Ideal.Quotient.liftₐ (KH.genIdeal y) (aeval y) (aeval_eq_zero_of_mem_genIdeal y)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evQ_mk (p : MRingOver ℚ ι) : evQ y (Ideal.Quotient.mk (KH.genIdeal y) p) = aeval y p := rfl

/- English proof (translation)
Take `⟨m, rfl⟩` from `Ideal.Quotient.mk_surjective m`. Use `show evQ y (Ideal.Quotient.mk _ (r * m)) = _`. Rewrite using `[evQ_mk, evQ_mk, map_mul]`.
-/
theorem evQ_smul (r : MRingOver ℚ ι) (m : MRingOver ℚ ι ⧸ KH.genIdeal y) :
    evQ y (r • m) = aeval y r * evQ y m := by
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
  show evQ y (Ideal.Quotient.mk _ (r * m)) = _
  rw [evQ_mk, evQ_mk, map_mul]

def NonzeroOn (I : ∀ k, Finset (ι k)) : Prop :=
  ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0

variable {y}

/- English proof (translation)
Unfold `KH.cellMon at ht`. Proceed by induction on `ht using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨k, i, hi, rfl⟩` from `hx`. Rewrite using `[aeval_X]`.

Conclude with `hI k i hi`. Consider the case `one => simp`. Consider the case `mul x z _ _ hx hz => rw [map_mul]`. Conclude with `mul_ne_zero hx hz`.
-/
theorem aeval_ne_zero_of_mem {I : ∀ k, Finset (ι k)} (hI : NonzeroOn y I) {t : MRingOver ℚ ι}
    (ht : t ∈ KH.cellMon ℚ I) : aeval y t ≠ 0 := by
  unfold KH.cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, hi, rfl⟩ := hx
    rw [aeval_X]
    exact hI k i hi
  | one => simp
  | mul x z _ _ hx hz => rw [map_mul]; exact mul_ne_zero hx hz

variable (y)

def ev (I : ∀ k, Finset (ι k)) (hI : NonzeroOn y I)
    (x : LocalizedModule (KH.cellMon ℚ I) (MRingOver ℚ ι ⧸ KH.genIdeal y)) : Ω :=
  LocalizedModule.liftOn x (fun p => evQ y p.1 / aeval y (p.2 : MRingOver ℚ ι)) (by
    rintro ⟨a, s⟩ ⟨b, t⟩ ⟨u, hu⟩
    simp only [Submonoid.smul_def] at hu
    have h := congrArg (evQ y) hu
    rw [evQ_smul, evQ_smul, evQ_smul, evQ_smul] at h
    have hu0 := aeval_ne_zero_of_mem hI u.2
    have hs0 := aeval_ne_zero_of_mem hI s.2
    have ht0 := aeval_ne_zero_of_mem hI t.2
    dsimp only
    rw [div_eq_div_iff hs0 ht0]
    have h' := mul_left_cancel₀ hu0 h
    linear_combination h')

/- English proof (translation)
The claim follows from `LocalizedModule.liftOn_mk _ _ _`.
-/
theorem ev_mk (I : ∀ k, Finset (ι k)) (hI : NonzeroOn y I) (m : MRingOver ℚ ι ⧸ KH.genIdeal y)
    (s : KH.cellMon ℚ I) : ev y I hI (LocalizedModule.mk m s) = evQ y m / aeval y (s : MRingOver ℚ ι) :=
  LocalizedModule.liftOn_mk _ _ _

def evHom (I : ∀ k, Finset (ι k)) (hI : NonzeroOn y I) :
    LocalizedModule (KH.cellMon ℚ I) (MRingOver ℚ ι ⧸ KH.genIdeal y) →+* Ω where
  toFun := ev y I hI
  map_one' := by
    rw [show (1 : LocalizedModule (KH.cellMon ℚ I) (MRingOver ℚ ι ⧸ KH.genIdeal y)) = LocalizedModule.mk 1 1 by
      rw [OreLocalization.one_def], ev_mk]
    simp
  map_mul' x x' := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      induction x' using LocalizedModule.induction_on with
      | h m' s' =>
        rw [LocalizedModule.mk_mul_mk, ev_mk, ev_mk, ev_mk, map_mul, Submonoid.coe_mul, map_mul]
        exact div_mul_div_comm _ _ _ _ |>.symm
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, ev_mk, map_zero, zero_div]
  map_add' x x' := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      induction x' using LocalizedModule.induction_on with
      | h m' s' =>
        have hs0 := aeval_ne_zero_of_mem hI s.2
        have hs0' := aeval_ne_zero_of_mem hI s'.2
        rw [LocalizedModule.mk_add_mk, ev_mk, ev_mk, ev_mk]
        simp only [Submonoid.smul_def, map_add, evQ_smul, Submonoid.coe_mul, map_mul]
        field_simp

/- English proof (translation)
The claim follows from `ev_mk y I hI m s`.
-/
theorem evHom_mk (I : ∀ k, Finset (ι k)) (hI : NonzeroOn y I) (m : MRingOver ℚ ι ⧸ KH.genIdeal y)
    (s : KH.cellMon ℚ I) :
    evHom y I hI (LocalizedModule.mk m s) = evQ y m / aeval y (s : MRingOver ℚ ι) :=
  ev_mk y I hI m s

/- English proof (translation)
Proceed by induction on `x using LocalizedModule.induction_on with`. Consider the case `h m s`. Rewrite using `[LocalizedModule.smul'_mk, evHom_mk, evHom_mk, map_smul, smul_div_assoc]`.
-/
theorem evHom_smul (I : ∀ k, Finset (ι k)) (hI : NonzeroOn y I) (q : ℚ)
    (x : LocalizedModule (KH.cellMon ℚ I) (MRingOver ℚ ι ⧸ KH.genIdeal y)) :
    evHom y I hI (q • x) = q • evHom y I hI x := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    rw [LocalizedModule.smul'_mk, evHom_mk, evHom_mk, map_smul, smul_div_assoc]

def evLin (I : ∀ k, Finset (ι k)) (hI : NonzeroOn y I) :
    LocalizedModule (KH.cellMon ℚ I) (MRingOver ℚ ι ⧸ KH.genIdeal y) →ₗ[ℚ] Ω where
  toFun := evHom y I hI
  map_add' := map_add _
  map_smul' := evHom_smul y I hI

/- English proof (translation)
Proceed by induction on `x using LocalizedModule.induction_on with`. Consider the case `h m t`. Rewrite using `[GenTwistGenerated.cellRes_mk (GenOnFibres.cellMon_mono hJI), evHom_mk, evHom_mk]`.
-/
theorem evHom_cellRes {J I : ∀ k, Finset (ι k)} (hJI : ∀ k, J k ⊆ I k) (hI : NonzeroOn y I)
    (hJ : NonzeroOn y J) (x : LocalizedModule (KH.cellMon ℚ J) (MRingOver ℚ ι ⧸ KH.genIdeal y)) :
    evHom y I hI (KH.cellRes ℚ (MRingOver ℚ ι ⧸ KH.genIdeal y) J I x) = evHom y J hJ x := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    rw [GenTwistGenerated.cellRes_mk (GenOnFibres.cellMon_mono hJI), evHom_mk, evHom_mk]

end Eval

section Glue

variable {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω)

/- English proof (translation)
Introduce `k i hi` and use `by rw [Finset.mem_singleton.mp hi]; exact hc k`.
-/
theorem nonzeroOn_chart {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : NonzeroOn y (chartCell c).1 :=
  fun k i hi => by rw [Finset.mem_singleton.mp hi]; exact hc k

open Classical in

def val (z : KH.CechC ℚ ι (MRingOver ℚ ι ⧸ KH.genIdeal y) 0) (c : ∀ k, ι k) : Ω :=
  if h : ∀ k, y ⟨k, c k⟩ ≠ 0 then evHom y _ (nonzeroOn_chart y h) (z (chartCell c)) else 0

/- English proof (translation)
The claim follows from `dif_pos hc`.
-/
theorem val_eq (z : KH.CechC ℚ ι (MRingOver ℚ ι ⧸ KH.genIdeal y) 0) {c : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : val y z c = evHom y _ (nonzeroOn_chart y hc) (z (chartCell c)) :=
  dif_pos hc

/- English proof (translation)
Distinguish the cases in `hbc : b = c k₀`. Substitute `hbc` using the available equality. Rewrite using `[Function.update_eq_self]`. Establish `hc' : ∀ k, y ⟨k, Function.update c k₀ b k⟩ ≠ 0`. Introduce `k`.

Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `hb`. Rewrite using `[Function.update_of_ne hk]`.

Conclude with `hc k`. Establish `hI : NonzeroOn y (pairCell c k₀ b hbc).1`. Introduce `k i hi`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality.

Simplify using `only [pairCell, Function.update_self, Finset.mem_insert, Finset.mem_singleton] at hi`. Break down `hi with rfl | rfl` into its components or cases. Conclude with `hc _`. Conclude with `hb`. Simplify using `only [pairCell, Function.update_of_ne hk, Finset.mem_singleton] at hi`.

Rewrite using `[hi]`. Conclude with `hc k`. Establish `hs1 : ∀ k, (chartCell c).1 k ⊆ (pairCell c k₀ b hbc).1 k`. Introduce `k`. Distinguish the cases in `hk : k = k₀`.

Substitute `hk` using the available equality. Simplify using `[chartCell, pairCell]`. Simplify using `[chartCell, pairCell, Function.update_of_ne hk]`. Establish `hs2 : ∀ k, (chartCell (Function.update c k₀ b)).1 k ⊆ (pairCell c k₀ b hbc).1 k`. Introduce `k`.

Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Simplify using `[chartCell, pairCell]`. Simplify using `[chartCell, pairCell, Function.update_of_ne hk]`. Establish `h1` using `congrArg (evHom y _ hI) (res_eq_pair c k₀ b hbc hz)`.

Rewrite `h1` using `[evHom_cellRes y hs1 hI (nonzeroOn_chart y hc), evHom_cellRes y hs2 hI (nonzeroOn_chart y hc')]`. Rewrite using `[val_eq y z hc', val_eq y z hc]`. Conclude with `h1.symm`.
-/
theorem val_update (z : KH.CechC ℚ ι (MRingOver ℚ ι ⧸ KH.genIdeal y) 0)
    (hz : KH.cechD ℚ ι (MRingOver ℚ ι ⧸ KH.genIdeal y) 0 z = 0) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (k₀ : K) (b : ι k₀) (hb : y ⟨k₀, b⟩ ≠ 0) : val y z (Function.update c k₀ b) = val y z c := by
  classical
  by_cases hbc : b = c k₀
  · subst hbc; rw [Function.update_eq_self]
  · have hc' : ∀ k, y ⟨k, Function.update c k₀ b k⟩ ≠ 0 := by
      intro k
      by_cases hk : k = k₀
      · subst hk; rw [Function.update_self]; exact hb
      · rw [Function.update_of_ne hk]; exact hc k
    have hI : NonzeroOn y (pairCell c k₀ b hbc).1 := by
      intro k i hi
      by_cases hk : k = k₀
      · subst hk
        simp only [pairCell, Function.update_self, Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact hc _
        · exact hb
      · simp only [pairCell, Function.update_of_ne hk, Finset.mem_singleton] at hi
        rw [hi]; exact hc k
    have hs1 : ∀ k, (chartCell c).1 k ⊆ (pairCell c k₀ b hbc).1 k := by
      intro k
      by_cases hk : k = k₀
      · subst hk; simp [chartCell, pairCell]
      · simp [chartCell, pairCell, Function.update_of_ne hk]
    have hs2 : ∀ k, (chartCell (Function.update c k₀ b)).1 k ⊆ (pairCell c k₀ b hbc).1 k := by
      intro k
      by_cases hk : k = k₀
      · subst hk; simp [chartCell, pairCell]
      · simp [chartCell, pairCell, Function.update_of_ne hk]
    have h1 := congrArg (evHom y _ hI) (res_eq_pair c k₀ b hbc hz)
    rw [evHom_cellRes y hs1 hI (nonzeroOn_chart y hc), evHom_cellRes y hs2 hI (nonzeroOn_chart y hc')] at h1
    rw [val_eq y z hc', val_eq y z hc]
    exact h1.symm

/- English proof (translation)
Establish `key : ∀ s : Finset K, val y z (fun k => if k ∈ s then c k else c₀ k) = val y z c₀`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert k s hk ih`.

Establish `e : (fun l => if l ∈ insert k s then c l else c₀ l) = Function.update (fun l => if l ∈ s then c l else c₀ l) k (c k)`. Use function extensionality and compare the values at `l`. Distinguish the cases in `hl : l = k`. Substitute `hl` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Function.update_of_ne hl]`. Simplify using `[Finset.mem_insert, hl]`. Apply the tactic sequence `rw [e, val_update y z hz _ (fun l => by by_cases h : l ∈ s <;> simp [h, hc l, hc₀ l]) k (c k) (hc k), ih]`. Simplify using `using key Finset.univ`.
-/
theorem val_eq_val (z : KH.CechC ℚ ι (MRingOver ℚ ι ⧸ KH.genIdeal y) 0)
    (hz : KH.cechD ℚ ι (MRingOver ℚ ι ⧸ KH.genIdeal y) 0 z = 0) (c₀ c : ∀ k, ι k)
    (hc₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : val y z c = val y z c₀ := by
  classical
  have key : ∀ s : Finset K, val y z (fun k => if k ∈ s then c k else c₀ k) = val y z c₀ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert k s hk ih =>
      have e : (fun l => if l ∈ insert k s then c l else c₀ l) =
          Function.update (fun l => if l ∈ s then c l else c₀ l) k (c k) := by
        funext l
        by_cases hl : l = k
        · subst hl; simp
        · rw [Function.update_of_ne hl]; simp [Finset.mem_insert, hl]
      rw [e, val_update y z hz _ (fun l => by by_cases h : l ∈ s <;> simp [h, hc l, hc₀ l]) k (c k) (hc k), ih]
  simpa using key Finset.univ

end Glue

section Integral

variable {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω)

def ratChart (c : ∀ k, ι k) : Submodule ℚ Ω where
  carrier := {w | ∃ D : ℕ, 0 < D ∧ (D : Ω) * w ∈ chartRingZ y c}
  zero_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro a b ⟨D₁, h₁, ha⟩ ⟨D₂, h₂, hb⟩
    refine ⟨D₁ * D₂, Nat.mul_pos h₁ h₂, ?_⟩
    have e : ((D₁ * D₂ : ℕ) : Ω) * (a + b) = (D₂ : Ω) * ((D₁ : Ω) * a) + (D₁ : Ω) * ((D₂ : Ω) * b) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) ha) (mul_mem (natCast_mem _ _) hb)
  smul_mem' := by
    rintro q w ⟨D, hD, hw⟩
    refine ⟨q.den * D, Nat.mul_pos q.den_pos hD, ?_⟩
    have hq : (q : Ω) * (q.den : Ω) = (q.num : Ω) := by
      have := congrArg (fun r : ℚ => (r : Ω)) (Rat.mul_den_eq_num q)
      push_cast at this
      exact this
    have e : ((q.den * D : ℕ) : Ω) * (q • w) = (q.num : Ω) * ((D : Ω) * w) := by
      rw [Rat.smul_def]
      push_cast
      linear_combination ((D : Ω) * w) * hq
    rw [e]
    exact mul_mem (intCast_mem _ _) hw

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_pos, by simpa using hw⟩`.
-/
theorem mem_ratChart_of_mem {c : ∀ k, ι k} {w : Ω} (hw : w ∈ chartRingZ y c) : w ∈ ratChart y c :=
  ⟨1, one_pos, by simpa using hw⟩

/- English proof (translation)
Rewrite using `[p.as_sum, map_sum, Finset.sum_mul]`. Use `Submodule.sum_mem _ fun μ hμ => ?_` and prove the remaining obligations. Establish `hdeg` using `hp μ hμ`. Rewrite using `[aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]`. Establish `key : (∏ p : Σ k, ι k, y p ^ μ p) * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) = ∏ p : Σ k, ι k, (y p / y ⟨p.1, c p.1⟩) ^ μ p`.

Rewrite using `[Finset.prod_congr rfl fun p _ => div_pow (y p) _ (μ p), Finset.prod_div_distrib]`. Establish `h2 : ∏ p : Σ k, ι k, y ⟨p.1, c p.1⟩ ^ μ p = ∏ k, y ⟨k, c k⟩ ^ d k`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, y ⟨k, c k⟩ ^ μ ⟨k, i⟩ = _`.

Rewrite using `[Finset.prod_pow_eq_pow_sum, hdeg k]`. Rewrite using `[h2, div_eq_mul_inv, ← Finset.prod_inv_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[zpow_neg, zpow_natCast]`.

Rewrite using `[mul_assoc, key, ← Algebra.smul_def]`. Use `Submodule.smul_mem _ _ (mem_ratChart_of_mem y ?_)` and prove the remaining obligations. Conclude with `Subalgebra.prod_mem _ fun p _ => Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) p)) _`.
-/
theorem aeval_homog_mem (c : ∀ k, ι k) {p : MRingOver ℚ ι} {d : K → ℕ} (hp : IsMultiHomog p d) :
    aeval y p * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) ∈ ratChart y c := by
  classical
  rw [p.as_sum, map_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hdeg := hp μ hμ
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  have key : (∏ p : Σ k, ι k, y p ^ μ p) * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) =
      ∏ p : Σ k, ι k, (y p / y ⟨p.1, c p.1⟩) ^ μ p := by
    rw [Finset.prod_congr rfl fun p _ => div_pow (y p) _ (μ p), Finset.prod_div_distrib]
    have h2 : ∏ p : Σ k, ι k, y ⟨p.1, c p.1⟩ ^ μ p = ∏ k, y ⟨k, c k⟩ ^ d k := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show ∏ i, y ⟨k, c k⟩ ^ μ ⟨k, i⟩ = _
      rw [Finset.prod_pow_eq_pow_sum, hdeg k]
    rw [h2, div_eq_mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [zpow_neg, zpow_natCast]
  rw [mul_assoc, key, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ (mem_ratChart_of_mem y ?_)
  exact Subalgebra.prod_mem _ fun p _ => Subalgebra.pow_mem _
    (Algebra.subset_adjoin (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) p)) _

/- English proof (translation)
Set `L : (MRingOver ℚ ι ⧸ KH.genIdeal y) →ₗ[ℚ] Ω` to `LinearMap.mulRight ℚ (∏ k, y ⟨k, c k⟩ ^ (-e k)) ∘ₗ (evQ y).toLinearMap`. Establish `hle : KH.quotPart ℚ (KH.genIdeal y) e ≤ (ratChart y c).comap L`. Unfold `KH.quotPart`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, ⟨hnn, hp⟩, rfl⟩`.

Express the relevant statement in the definitionally equal form `evQ y (Ideal.Quotient.mk _ p) * ∏ k, y ⟨k, c k⟩ ^ (-e k) ∈ ratChart y c`. Rewrite using `[evQ_mk]`. Establish `h` using `aeval_homog_mem y c hp`. Establish `h' : ∀ k, (((e k).toNat : ℕ) : ℤ) = e k` using `fun k => Int.toNat_of_nonneg (hnn k)`. Simplify using `only [h'] at h`.

Conclude with `h`. Conclude with `hle hm`.
-/
theorem evQ_quotPart_mem (c : ∀ k, ι k) {e : K → ℤ} {m : MRingOver ℚ ι ⧸ KH.genIdeal y}
    (hm : m ∈ KH.quotPart ℚ (KH.genIdeal y) e) : evQ y m * ∏ k, y ⟨k, c k⟩ ^ (-e k) ∈ ratChart y c := by
  let L : (MRingOver ℚ ι ⧸ KH.genIdeal y) →ₗ[ℚ] Ω :=
    LinearMap.mulRight ℚ (∏ k, y ⟨k, c k⟩ ^ (-e k)) ∘ₗ (evQ y).toLinearMap
  have hle : KH.quotPart ℚ (KH.genIdeal y) e ≤ (ratChart y c).comap L := by
    unfold KH.quotPart
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, ⟨hnn, hp⟩, rfl⟩
    change evQ y (Ideal.Quotient.mk _ p) * ∏ k, y ⟨k, c k⟩ ^ (-e k) ∈ ratChart y c
    rw [evQ_mk]
    have h := aeval_homog_mem y c hp
    have h' : ∀ k, (((e k).toNat : ℕ) : ℤ) = e k := fun k => Int.toNat_of_nonneg (hnn k)
    simp only [h'] at h
    exact h
  exact hle hm

/- English proof (translation)
Unfold `KH.cellMon at ht`. Proceed by induction on `ht using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨k, i, hi, rfl⟩` from `hx`. Establish `hik : i = c k` using `Finset.mem_singleton.mp hi`.

Substitute `hik` using the available equality. Use `⟨Pi.single k 1, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (fun h => absurd (Finset.mem_univ k) h)]`. Simplify using the standard rewrite rules. Consider the case `one => exact ⟨0, by simp⟩`.

Consider the case `mul x z _ _ hx hz`. Take `⟨e, rfl⟩` from `hx`. Take `⟨e', rfl⟩` from `hz`. Conclude with `⟨e + e', by simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]⟩`.
-/
theorem mem_cellMon_chart {c : ∀ k, ι k} {t : MRingOver ℚ ι} (ht : t ∈ KH.cellMon ℚ (chartCell c).1) :
    ∃ e : K → ℕ, t = ∏ k, X ⟨k, c k⟩ ^ e k := by
  classical
  unfold KH.cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, hi, rfl⟩ := hx
    have hik : i = c k := Finset.mem_singleton.mp hi
    subst hik
    refine ⟨Pi.single k 1, ?_⟩
    rw [Finset.prod_eq_single k (fun k' _ hk' => by simp [hk'])
      (fun h => absurd (Finset.mem_univ k) h)]
    simp
  | one => exact ⟨0, by simp⟩
  | mul x z _ _ hx hz =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨e', rfl⟩ := hz
    exact ⟨e + e', by simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]⟩

/- English proof (translation)
Use `GenOnFibres.homog_map (Int.castRingHom ℚ) (GenOnFibres.homog_cmon c e)` as an intermediate fact. Simplify `this` using `[GenOnFibres.cmon, map_prod]`.
-/
theorem homog_prod_X (c : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRingOver ℚ ι) ^ e k) e := by
  have := GenOnFibres.homog_map (Int.castRingHom ℚ) (GenOnFibres.homog_cmon c e)
  simpa [GenOnFibres.cmon, map_prod] using this

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (X_ne_zero _)`.
-/
theorem prod_X_ne_zero (c : ∀ k, ι k) (e : K → ℕ) : (∏ k, (X ⟨k, c k⟩ : MRingOver ℚ ι) ^ e k) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (X_ne_zero _)

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : f.support.Nonempty := by`. Rewrite using `[Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]`. Conclude with `hf`. Use function extensionality and compare the values at `k`. Rewrite using `[← ha m hm k, hb m hm k]`.
-/
theorem eq_of_homog {f : MRingOver ℚ ι} {a b : K → ℕ} (ha : IsMultiHomog f a) (hb : IsMultiHomog f b)
    (hf : f ≠ 0) : a = b := by
  obtain ⟨m, hm⟩ : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hf
  funext k
  rw [← ha m hm k, hb m hm k]

/- English proof (translation)
Set `L` to `LinearMap.mulRight ℚ (∏ k, y ⟨k, c k⟩ ^ (-n k)) ∘ₗ evLin y _ (nonzeroOn_chart y hc)`. Establish `hle : KH.locPart ι (KH.quotPart ℚ (KH.genIdeal y)) (KH.cellMon ℚ (chartCell c).1) n ≤ (ratChart y c).comap L`. Unfold `KH.locPart`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨m, t, a, ht, hm, rfl⟩`.

Express the relevant statement in the definitionally equal form `evHom y _ (nonzeroOn_chart y hc) (LocalizedModule.mk m t) * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ ratChart y c`. Rewrite using `[evHom_mk]`. Take `⟨e, he⟩` from `mem_cellMon_chart t.2`. Establish `hea : a = e` using `eq_of_homog ht (by rw [he]; exact homog_prod_X c e) (by rw [he]; exact prod_X_ne_zero c e)`. Establish `hval : aeval y (t : MRingOver ℚ ι) = ∏ k, y ⟨k, c k⟩ ^ a k`.

Rewrite using `[he, hea]`. Simplify using `[map_prod]`. Establish `key : evQ y m / aeval y (t : MRingOver ℚ ι) * ∏ k, y ⟨k, c k⟩ ^ (-n k) = evQ y m * ∏ k, y ⟨k, c k⟩ ^ (-(n + fun k => (a k : ℤ)) k)`. Rewrite using `[hval, div_mul_eq_mul_div, mul_div_assoc]`. Use `congr 1`.

Rewrite using `[← Finset.prod_div_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show _ = y ⟨k, c k⟩ ^ (-(n k + (a k : ℤ)))`. Rewrite using `[neg_add, zpow_add₀ (hc k), zpow_neg _ (a k : ℤ), zpow_natCast, div_eq_mul_inv]`. Rewrite using `[key]`.

Conclude with `evQ_quotPart_mem y c hm`. Conclude with `hle hx`.
-/
theorem ev_locPart_mem (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {n : K → ℤ}
    {x : LocalizedModule (KH.cellMon ℚ (chartCell c).1) (MRingOver ℚ ι ⧸ KH.genIdeal y)}
    (hx : x ∈ KH.locPart ι (KH.quotPart ℚ (KH.genIdeal y)) (KH.cellMon ℚ (chartCell c).1) n) :
    evHom y _ (nonzeroOn_chart y hc) x * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ ratChart y c := by
  let L := LinearMap.mulRight ℚ (∏ k, y ⟨k, c k⟩ ^ (-n k)) ∘ₗ evLin y _ (nonzeroOn_chart y hc)
  have hle : KH.locPart ι (KH.quotPart ℚ (KH.genIdeal y)) (KH.cellMon ℚ (chartCell c).1) n ≤
      (ratChart y c).comap L := by
    unfold KH.locPart
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, t, a, ht, hm, rfl⟩
    change evHom y _ (nonzeroOn_chart y hc) (LocalizedModule.mk m t) * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ ratChart y c
    rw [evHom_mk]
    obtain ⟨e, he⟩ := mem_cellMon_chart t.2
    have hea : a = e := eq_of_homog ht (by rw [he]; exact homog_prod_X c e) (by rw [he]; exact prod_X_ne_zero c e)
    have hval : aeval y (t : MRingOver ℚ ι) = ∏ k, y ⟨k, c k⟩ ^ a k := by
      rw [he, hea]; simp [map_prod]
    have key : evQ y m / aeval y (t : MRingOver ℚ ι) * ∏ k, y ⟨k, c k⟩ ^ (-n k) =
        evQ y m * ∏ k, y ⟨k, c k⟩ ^ (-(n + fun k => (a k : ℤ)) k) := by
      rw [hval, div_mul_eq_mul_div, mul_div_assoc]
      congr 1
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      show _ = y ⟨k, c k⟩ ^ (-(n k + (a k : ℤ)))
      rw [neg_add, zpow_add₀ (hc k), zpow_neg _ (a k : ℤ), zpow_natCast, div_eq_mul_inv]
    rw [key]
    exact evQ_quotPart_mem y c hm
  exact hle hx

end Integral

/- English proof (translation)
Distinguish the cases in `hall : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0`. Use `swap`. Use `push Not at hall`. Take `⟨k, hk⟩` from `hall`. Conclude with `⟨1, fun c hc => absurd (hk (c k)) (hc k), one_ne_zero⟩`.

Use `choose c₀ hc₀ using hall`. Take `⟨r, z, u, hz, -, hsum⟩` from `hG (chartCell c₀)`. Establish `h1` using `congrArg (evHom y _ (nonzeroOn_chart y hc₀)) hsum`. Rewrite `h1` using `[map_sum, map_one]`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, evHom y _ (nonzeroOn_chart y hc₀) (z j (chartCell c₀)) ≠ 0 := by`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Simplify using `only [map_mul, hcon, mul_zero, Finset.sum_const_zero] at h1`. Conclude with `zero_ne_one h1`. Establish `hZ` using `hz j`.

Establish `hZd` using `(Submodule.mem_inf.mp hZ).2`. Rewrite `hZd` using `[Submodule.restrictScalars_mem, LinearMap.mem_ker]`. Establish `hZc` using `(Submodule.mem_inf.mp hZ).1`. Unfold `KH.cechCc at hZc`. Rewrite `hZc` using `[Submodule.mem_pi]`.

Establish `hv : val y (z j) c₀ ≠ 0` using `by rw [val_eq y (z j) hc₀]; exact hj`. Establish `hD : ∀ c : ∀ k, ι k, ∃ D : ℕ, 0 < D ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) → (D : Ω) * (val y (z j) c₀ * ∏ k, y ⟨k, c k⟩ ^ (-n k)) ∈ chartRingZ y c)`. Introduce `c`. Distinguish the cases in `hc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Take `⟨D, hD, hmem⟩` from `ev_locPart_mem y c hc (hZc (chartCell c) (Set.mem_univ _))`.

Use `⟨D, hD, fun _ => ?_⟩` and prove the remaining obligations. Rewrite using `[← val_eq_val y (z j) hZd c₀ c hc₀ hc, val_eq y (z j) hc]`. Conclude with `hmem`. Conclude with `⟨1, one_pos, fun h => absurd h hc⟩`. Use `choose D hDpos hDmem using hD`.

Use `⟨((∏ c, D c : ℕ) : Ω) * val y (z j) c₀, ?_, ?_⟩` and prove the remaining obligations. Introduce `c hc`. Simplify using `only [Nat.cast_one, one_mul]`. Establish `e : ((∏ c, D c : ℕ) : Ω) * val y (z j) c₀ * ∏ k, y ⟨k, c k⟩ ^ (-n k) = ((∏ c' ∈ Finset.univ.erase c, D c' : ℕ) : Ω) * ((D c : Ω) * (val y (z j) c₀ * ∏ k, y ⟨k, c k⟩ ^ (-n k)))`. Rewrite using `[← Finset.mul_prod_erase Finset.univ D (Finset.mem_univ c)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_mem (natCast_mem _ _) (hDmem c hc)`. Conclude with `mul_ne_zero (Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun c _ => (hDpos c).ne')) hv`.
-/
theorem exists_section {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (n : K → ℤ)
    (hG : KH.GeneratedV ℚ (KH.genIdeal y) n) : ∃ s ∈ chartLat y n 1, s ≠ 0 := by
  classical
  by_cases hall : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0
  swap
  · push Not at hall
    obtain ⟨k, hk⟩ := hall
    exact ⟨1, fun c hc => absurd (hk (c k)) (hc k), one_ne_zero⟩
  choose c₀ hc₀ using hall
  obtain ⟨r, z, u, hz, -, hsum⟩ := hG (chartCell c₀)
  have h1 := congrArg (evHom y _ (nonzeroOn_chart y hc₀)) hsum
  rw [map_sum, map_one] at h1
  obtain ⟨j, hj⟩ : ∃ j, evHom y _ (nonzeroOn_chart y hc₀) (z j (chartCell c₀)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp only [map_mul, hcon, mul_zero, Finset.sum_const_zero] at h1
    exact zero_ne_one h1
  have hZ := hz j
  have hZd := (Submodule.mem_inf.mp hZ).2
  rw [Submodule.restrictScalars_mem, LinearMap.mem_ker] at hZd
  have hZc := (Submodule.mem_inf.mp hZ).1
  unfold KH.cechCc at hZc
  rw [Submodule.mem_pi] at hZc
  have hv : val y (z j) c₀ ≠ 0 := by rw [val_eq y (z j) hc₀]; exact hj
  have hD : ∀ c : ∀ k, ι k, ∃ D : ℕ, 0 < D ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      (D : Ω) * (val y (z j) c₀ * ∏ k, y ⟨k, c k⟩ ^ (-n k)) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨D, hD, hmem⟩ := ev_locPart_mem y c hc (hZc (chartCell c) (Set.mem_univ _))
      refine ⟨D, hD, fun _ => ?_⟩
      rw [← val_eq_val y (z j) hZd c₀ c hc₀ hc, val_eq y (z j) hc]
      exact hmem
    · exact ⟨1, one_pos, fun h => absurd h hc⟩
  choose D hDpos hDmem using hD
  refine ⟨((∏ c, D c : ℕ) : Ω) * val y (z j) c₀, ?_, ?_⟩
  · intro c hc
    simp only [Nat.cast_one, one_mul]
    have e : ((∏ c, D c : ℕ) : Ω) * val y (z j) c₀ * ∏ k, y ⟨k, c k⟩ ^ (-n k) =
        ((∏ c' ∈ Finset.univ.erase c, D c' : ℕ) : Ω) *
          ((D c : Ω) * (val y (z j) c₀ * ∏ k, y ⟨k, c k⟩ ^ (-n k))) := by
      rw [← Finset.mul_prod_erase Finset.univ D (Finset.mem_univ c)]
      push_cast
      ring
    rw [e]
    exact mul_mem (natCast_mem _ _) (hDmem c hc)
  · exact mul_ne_zero (Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun c _ => (hDpos c).ne')) hv

end GeneratedNonzeroSection

/- English proof (translation)
Introduce `K _ _ ι _ _ Ω _ _ y n hG`. Conclude with `GeneratedNonzeroSection.exists_section y n hG`.
-/
theorem GeneratedNonzeroSection.proof : GeneratedNonzeroSection.Statement := by
  intro K _ _ ι _ _ Ω _ _ y n hG
  exact GeneratedNonzeroSection.exists_section y n hG

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
