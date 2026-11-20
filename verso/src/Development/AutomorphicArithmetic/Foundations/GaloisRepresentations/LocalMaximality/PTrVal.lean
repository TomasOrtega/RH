import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibFiniteAndSep
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.productCup_of_system.PartialTraceValue

/- English proof (translation)
Set `N : Submodule A B` to `𝔟.restrictScalars A`. Establish `key : ∀ j ∈ I.map (algebraMap A B), ∀ b : B, (Submodule.Quotient.mk (j * b) : B ⧸ N) ∈ I • (⊤ : Submodule A (B ⧸ N))`. Introduce `j hj`. Use `Submodule.span_induction ?_ ?_ ?_ ?_ hj` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩ b`.

Rewrite using `[← Algebra.smul_def, Submodule.Quotient.mk_smul]`. Conclude with `Submodule.smul_mem_smul hi Submodule.mem_top`. Introduce `b`. Rewrite using `[zero_mul]`. Conclude with `Submodule.zero_mem _`.

Introduce `u v _ _ hu hv b`. Rewrite using `[add_mul, Submodule.Quotient.mk_add]`. Conclude with `Submodule.add_mem _ (hu b) (hv b)`. Introduce `c u _ hu b`. Rewrite using `[smul_eq_mul, show c * u * b = u * (c * b) by ring]`.

Conclude with `hu _`. Establish `hin : (⊤ : Submodule A (B ⧸ N)) ≤ I • ⊤`. Introduce and unpack `q -`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨a, ha, j, hj, haj⟩` from `Submodule.mem_sup.1 (hb ▸ Submodule.mem_top : (1 : B) ∈ 𝔟 ⊔ I.map (algebraMap A B))`.

Establish `: (Submodule.Quotient.mk b : B ⧸ N) = Submodule.Quotient.mk (j * b)`. Rewrite using `[Submodule.Quotient.eq]`. Establish `: b - j * b = a * b`. Take the linear combination `(-b) * haj`. Rewrite using `[this]`.

Conclude with `𝔟.mul_mem_right b ha`. Rewrite using `[this]`. Conclude with `key j hj b`. Take `⟨r, hr1, hr⟩` from `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I (⊤ : Submodule A (B ⧸ N)) Module.Finite.fg_top hin`. Use `⟨r, hr1, ?_⟩` and prove the remaining obligations.

Establish `h0` using `hr (Submodule.Quotient.mk 1) Submodule.mem_top`. Rewrite `h0` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Algebra.smul_def, mul_one]`. Conclude with `h0`.
-/
private theorem nakGen {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] (I : Ideal A) (𝔟 : Ideal B)
    (hb : 𝔟 ⊔ I.map (algebraMap A B) = ⊤) : ∃ r : A, r - 1 ∈ I ∧ algebraMap A B r ∈ 𝔟 := by
  let N : Submodule A B := 𝔟.restrictScalars A
  have key : ∀ j ∈ I.map (algebraMap A B), ∀ b : B,
      (Submodule.Quotient.mk (j * b) : B ⧸ N) ∈ I • (⊤ : Submodule A (B ⧸ N)) := by
    intro j hj
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hj
    · rintro _ ⟨i, hi, rfl⟩ b
      rw [← Algebra.smul_def, Submodule.Quotient.mk_smul]
      exact Submodule.smul_mem_smul hi Submodule.mem_top
    · intro b
      rw [zero_mul]
      exact Submodule.zero_mem _
    · intro u v _ _ hu hv b
      rw [add_mul, Submodule.Quotient.mk_add]
      exact Submodule.add_mem _ (hu b) (hv b)
    · intro c u _ hu b
      rw [smul_eq_mul, show c * u * b = u * (c * b) by ring]
      exact hu _
  have hin : (⊤ : Submodule A (B ⧸ N)) ≤ I • ⊤ := by
    rintro q -
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨a, ha, j, hj, haj⟩ := Submodule.mem_sup.1 (hb ▸ Submodule.mem_top : (1 : B) ∈ 𝔟 ⊔ I.map (algebraMap A B))
    have : (Submodule.Quotient.mk b : B ⧸ N) = Submodule.Quotient.mk (j * b) := by
      rw [Submodule.Quotient.eq]
      have : b - j * b = a * b := by
        linear_combination (-b) * haj
      rw [this]
      exact 𝔟.mul_mem_right b ha
    rw [this]
    exact key j hj b
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
    (⊤ : Submodule A (B ⧸ N)) Module.Finite.fg_top hin
  refine ⟨r, hr1, ?_⟩
  have h0 := hr (Submodule.Quotient.mk 1) Submodule.mem_top
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Algebra.smul_def, mul_one] at h0
  exact h0

/- English proof (translation)
Use `letI alg : Algebra A B := φ.toRingHom.toAlgebra`. Use `haveI tow : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm`. Use `haveI int : Algebra.IsIntegral A B := ⟨hint⟩`. Use `haveI : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType ℂ _ _`. Use `haveI fin : Module.Finite A B := Algebra.IsIntegral.finite`.

Conclude with `nakGen I 𝔟 hb`.
-/
private theorem nakHom {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    (φ : A →ₐ[ℂ] B) (hint : ∀ b : B, φ.toRingHom.IsIntegralElem b) (I : Ideal A) (𝔟 : Ideal B)
    (hb : 𝔟 ⊔ I.map φ.toRingHom = ⊤) : ∃ r : A, r - 1 ∈ I ∧ φ r ∈ 𝔟 := by
  letI alg : Algebra A B := φ.toRingHom.toAlgebra
  haveI tow : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  haveI int : Algebra.IsIntegral A B := ⟨hint⟩
  haveI : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType ℂ _ _
  haveI fin : Module.Finite A B := Algebra.IsIntegral.finite
  exact nakGen I 𝔟 hb

variable {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L] [IsScalarTower ℂ F L]
  {d : ℕ} (x : Fin (d + 1) → F)

private def tA (j : Fin d) : rA ℂ x {0} :=
  ⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩

private def IA : Ideal (rA ℂ x {0}) := Ideal.span (Set.range (tA x))

/- English proof (translation)
Establish `hle : IA x ≤ RingHom.ker φ`. Rewrite using `[IA, Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `hφ j`. Use `hle hr` as an intermediate fact.

Rewrite `this` using `[RingHom.mem_ker, map_sub, map_one, sub_eq_zero]`. Conclude with `this`.
-/
private theorem val_one (φ : rA ℂ x {0} →ₐ[ℂ] ℂ) (hφ : ∀ j, φ (tA x j) = 0) {r : rA ℂ x {0}}
    (hr : r - 1 ∈ IA x) : φ r = 1 := by
  have hle : IA x ≤ RingHom.ker φ := by
    rw [IA, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hφ j
  have := hle hr
  rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
  exact this

/- English proof (translation)
Use `haveI := h.smooth 0`. Establish `hcomp : (rB ℂ L x {0}).val.toRingHom.comp (FibFin.incl ℂ L x).toRingHom = algebraMap (rA ℂ x {0}) L` using `RingHom.ext fun a => rfl`. Establish `hint : ∀ b : rB ℂ L x {0}, (FibFin.incl ℂ L x).toRingHom.IsIntegralElem b` using `fun b => by`. Take `⟨p, hpm, hp⟩ : IsIntegral (rA ℂ x {0}) (b : L)` from `b.2`. Use `⟨p, hpm, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(rB ℂ L x {0}).val.toRingHom (Polynomial.eval₂ (FibFin.incl ℂ L x).toRingHom b p) = (0 : L)`. Rewrite using `[Polynomial.hom_eval₂, hcomp]`. Conclude with `hp`. Establish `hJ : FibFin.coordIdeal ℂ L x ≤ (IA x).map (FibFin.incl ℂ L x).toRingHom`.

Rewrite using `[FibFin.coordIdeal, Ideal.span_le]`. Introduce and unpack `_ ⟨l, rfl⟩`. Express the relevant statement in the definitionally equal form `(FibFin.incl ℂ L x).toRingHom (tA x l) ∈ _`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self l))`. Conclude with `nakHom (FibFin.incl ℂ L x) hint (IA x) 𝔟 (top_le_iff.1 (hb ▸ sup_le_sup_left hJ 𝔟))`.
-/
private theorem nak (h : IsFinCover ℂ L x) (𝔟 : Ideal (rB ℂ L x {0}))
    (hb : 𝔟 ⊔ FibFin.coordIdeal ℂ L x = ⊤) :
    ∃ r : rA ℂ x {0}, r - 1 ∈ IA x ∧ FibFin.incl ℂ L x r ∈ 𝔟 := by
  haveI := h.smooth 0
  have hcomp : (rB ℂ L x {0}).val.toRingHom.comp (FibFin.incl ℂ L x).toRingHom =
      algebraMap (rA ℂ x {0}) L := RingHom.ext fun a => rfl
  have hint : ∀ b : rB ℂ L x {0}, (FibFin.incl ℂ L x).toRingHom.IsIntegralElem b := fun b => by
    obtain ⟨p, hpm, hp⟩ : IsIntegral (rA ℂ x {0}) (b : L) := b.2
    refine ⟨p, hpm, ?_⟩
    apply Subtype.ext
    change (rB ℂ L x {0}).val.toRingHom (Polynomial.eval₂ (FibFin.incl ℂ L x).toRingHom b p) = (0 : L)
    rw [Polynomial.hom_eval₂, hcomp]
    exact hp
  have hJ : FibFin.coordIdeal ℂ L x ≤ (IA x).map (FibFin.incl ℂ L x).toRingHom := by
    rw [FibFin.coordIdeal, Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    change (FibFin.incl ℂ L x).toRingHom (tA x l) ∈ _
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self l))
  exact nakHom (FibFin.incl ℂ L x) hint (IA x) 𝔟 (top_le_iff.1 (hb ▸ sup_le_sup_left hJ 𝔟))

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hall` using `(FibFin.fib_finite_and_sep ℂ L x h hred).2 1 (fun e => (hne ⟨e⟩).elim)`. Establish `ht : FibFin.coordIdeal ℂ L x = ⊤` using `(Ideal.eq_top_iff_one _).2 hall`. Take `⟨r, hr1, hr⟩` from `nak x h ⊥ (by rw [ht]; simp)`. Establish `hr0 : r = 0`.

Establish `h0 : algebraMap F L (r : F) = 0` using `congrArg Subtype.val ((Ideal.mem_bot).1 hr)`. Conclude with `Subtype.ext ((map_eq_zero _).1 h0)`. Take `⟨e, he⟩` from `rA_single_polyEquiv ℂ F d x h.pd 0`. Establish `hε : ((MvPolynomial.aeval (0 : Fin d → ℂ)).comp e.symm.toAlgHom) r = 1`. Use `val_one x _ (fun j => ?_) hr1` and prove the remaining obligations.

Establish `htj : tA x j = e (MvPolynomial.X j)` using `Subtype.ext (by rw [he j, Fin.succAbove_zero]; rfl)`. Rewrite using `[htj]`. Simplify using the standard rewrite rules. Rewrite `hε` using `[hr0, map_zero]`. Conclude with `zero_ne_one hε`.
-/
private theorem fib_nonempty (h : IsFinCover ℂ L x)
    (hred : IsReduced (rB ℂ L x {0} ⧸ FibFin.coordIdeal ℂ L x)) : Nonempty (fib ℂ L x) := by
  by_contra hne
  have hall := (FibFin.fib_finite_and_sep ℂ L x h hred).2 1 (fun e => (hne ⟨e⟩).elim)
  have ht : FibFin.coordIdeal ℂ L x = ⊤ := (Ideal.eq_top_iff_one _).2 hall
  obtain ⟨r, hr1, hr⟩ := nak x h ⊥ (by rw [ht]; simp)
  have hr0 : r = 0 := by
    have h0 : algebraMap F L (r : F) = 0 := congrArg Subtype.val ((Ideal.mem_bot).1 hr)
    exact Subtype.ext ((map_eq_zero _).1 h0)
  obtain ⟨e, he⟩ := rA_single_polyEquiv ℂ F d x h.pd 0
  have hε : ((MvPolynomial.aeval (0 : Fin d → ℂ)).comp e.symm.toAlgHom) r = 1 := by
    refine val_one x _ (fun j => ?_) hr1
    have htj : tA x j = e (MvPolynomial.X j) := Subtype.ext (by rw [he j, Fin.succAbove_zero]; rfl)
    rw [htj]
    simp
  rw [hr0, map_zero] at hε
  exact zero_ne_one hε

/- English proof (translation)
Take `⟨hfin, hsep⟩` from `FibFin.fib_finite_and_sep ℂ L x h hred`. Use `haveI := Fintype.ofFinite (fib ℂ L x)`. Use `choose b hb hb0 using h𝔞`. Use `choose c hc using fun e0 : fib ℂ L x => hCRT (fun e => if e = e0 then (e0.1 (b e0))⁻¹ else 0)`. Establish `hs : (∑ e0, c e0 * b e0) ∈ 𝔞` using `Ideal.sum_mem _ fun e0 _ => 𝔞.mul_mem_left _ (hb e0)`.

Establish `hval : ∀ e : fib ℂ L x, e.1 (∑ e0, c e0 * b e0) = 1`. Introduce `e`. Rewrite using `[map_sum, Finset.sum_eq_single e (fun e0 _ hne => by rw [map_mul, hc, if_neg (Ne.symm hne), zero_mul]) (fun hn => (hn (Finset.mem_univ e)).elim), map_mul, hc, if_pos rfl]`. Conclude with `inv_mul_cancel₀ (hb0 e)`. Establish `h1` using `hsep (1 - ∑ e0, c e0 * b e0) (fun e => by rw [map_sub, map_one, hval, sub_self])`.

Rewrite using `[Ideal.eq_top_iff_one]`. Conclude with `Submodule.mem_sup.2 ⟨_, hs, _, h1, by ring⟩`.
-/
private theorem comax (h : IsFinCover ℂ L x)
    (hred : IsReduced (rB ℂ L x {0} ⧸ FibFin.coordIdeal ℂ L x))
    (hCRT : ∀ v : fib ℂ L x → ℂ, ∃ b : rB ℂ L x {0}, ∀ e : fib ℂ L x, e.1 b = v e)
    (𝔞 : Ideal (rB ℂ L x {0})) (h𝔞 : ∀ e : fib ℂ L x, ∃ b ∈ 𝔞, e.1 b ≠ 0) :
    𝔞 ⊔ FibFin.coordIdeal ℂ L x = ⊤ := by
  obtain ⟨hfin, hsep⟩ := FibFin.fib_finite_and_sep ℂ L x h hred
  haveI := Fintype.ofFinite (fib ℂ L x)
  classical
  choose b hb hb0 using h𝔞
  choose c hc using fun e0 : fib ℂ L x => hCRT (fun e => if e = e0 then (e0.1 (b e0))⁻¹ else 0)
  have hs : (∑ e0, c e0 * b e0) ∈ 𝔞 := Ideal.sum_mem _ fun e0 _ => 𝔞.mul_mem_left _ (hb e0)
  have hval : ∀ e : fib ℂ L x, e.1 (∑ e0, c e0 * b e0) = 1 := by
    intro e
    rw [map_sum, Finset.sum_eq_single e (fun e0 _ hne => by rw [map_mul, hc, if_neg (Ne.symm hne), zero_mul])
      (fun hn => (hn (Finset.mem_univ e)).elim), map_mul, hc, if_pos rfl]
    exact inv_mul_cancel₀ (hb0 e)
  have h1 := hsep (1 - ∑ e0, c e0 * b e0) (fun e => by rw [map_sub, map_one, hval, sub_self])
  rw [Ideal.eq_top_iff_one]
  exact Submodule.mem_sup.2 ⟨_, hs, _, h1, by ring⟩

/- English proof (translation)
Set `𝔞 : Ideal (rB ℂ L x {0})` to `{ carrier := {b | (b : L) * g ∈ rB ℂ L x {0}} add_mem' := by`. Introduce `a b ha hb`. Use `(rB ℂ L x {0}).add_mem ha hb` as an intermediate fact. Simplify `this` using `[add_mul]`. Use the proof step `zero_mem' := by simpa using (rB ℂ L x {0}).zero_mem`.

Use the proof step `smul_mem' := by`. Introduce `c b hb`. Use `(rB ℂ L x {0}).mul_mem c.2 hb` as an intermediate fact. Simplify `this }` using `[mul_assoc]`. Establish `h𝔞 : ∀ e : fib ℂ L x, ∃ b ∈ 𝔞, e.1 b ≠ 0` using `fun e => by`.

Take `⟨b, hb, hbv, hne, -⟩` from `hg e`. Conclude with `⟨⟨b, hb⟩, hbv, hne⟩`. Take `⟨s, hs1, hs⟩` from `nak x h 𝔞 (comax x h hred hCRT 𝔞 h𝔞)`. Establish `hs' : algebraMap F L (s : F) * g ∈ rB ℂ L x {0}` using `hs`. Establish `hone : ∀ e : fib ℂ L x, e.1 (FibFin.incl ℂ L x s) = 1` using `fun e => val_one x (e.1.comp (FibFin.incl ℂ L x)) (fun j => e.2 j) hs1`.

Establish `hval : ∀ e : fib ℂ L x, e.1 ⟨_, hs'⟩ = γ e`. Introduce `e`. Take `⟨b, hb, hbv, hne, heq⟩` from `hg e`. Establish `h1 : (⟨b, hb⟩ : rB ℂ L x {0}) * ⟨_, hs'⟩ = FibFin.incl ℂ L x s * ⟨b * g, hbv⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `b * (algebraMap F L (s : F) * g) = algebraMap F L (s : F) * (b * g)`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `congrArg e.1 h1`. Rewrite `h2` using `[map_mul, map_mul, hone, one_mul, heq]`. Conclude with `mul_left_cancel₀ hne h2`.

Take `⟨e0⟩` from `fib_nonempty x h hred`. Establish `hev : ∀ f : rA ℂ x {0}, e0.1 (FibFin.incl ℂ L x f) = ρ f`. Introduce `f`. Take `⟨b, hb, hbv, hne, heq⟩` from `hRes e0 f f.2`. Establish `h1 : (⟨b * algebraMap F L f, hbv⟩ : rB ℂ L x {0}) = ⟨b, hb⟩ * FibFin.incl ℂ L x f` using `rfl`.

Rewrite `heq` using `[h1, map_mul]`. Conclude with `mul_left_cancel₀ hne heq`. Establish `htr : Algebra.trace F L (algebraMap F L (s : F) * g) = (s : F) * Algebra.trace F L g`. Rewrite using `[← Algebra.smul_def, map_smul, smul_eq_mul]`. Establish `h3 : ρ ((s : F) * Algebra.trace F L g) = ρ (Algebra.trace F L g)`.

Establish `h4` using `hev (s * ⟨_, ht⟩)`. Rewrite `h4` using `[map_mul, map_mul, hone e0, one_mul, hev]`. Conclude with `h4.symm`. Rewrite using `[← h3, ← htr]`. Conclude with `(hRT ⟨_, hs'⟩).trans (finsum_congr hval)`.
-/
private theorem partialTrace_valuation_sum (h : IsFinCover ℂ L x)
    (hred : IsReduced (rB ℂ L x {0} ⧸ FibFin.coordIdeal ℂ L x)) (ρ : F →ₗ[ℂ] ℂ)
    (hRT : ∀ b : rB ℂ L x {0}, ρ (Algebra.trace F L b) = ∑ᶠ e : fib ℂ L x, e.1 b)
    (hRes : ∀ e : fib ℂ L x, ∀ f ∈ rA ℂ x {0}, Val (rB ℂ L x {0}) e.1 (algebraMap F L f) (ρ f))
    (hCRT : ∀ v : fib ℂ L x → ℂ, ∃ b : rB ℂ L x {0}, ∀ e : fib ℂ L x, e.1 b = v e)
    (g : L) (γ : fib ℂ L x → ℂ) (hg : ∀ e : fib ℂ L x, Val (rB ℂ L x {0}) e.1 g (γ e))
    (ht : Algebra.trace F L g ∈ rA ℂ x {0}) :
    ρ (Algebra.trace F L g) = ∑ᶠ e, γ e := by
  let 𝔞 : Ideal (rB ℂ L x {0}) :=
    { carrier := {b | (b : L) * g ∈ rB ℂ L x {0}}
      add_mem' := by
        intro a b ha hb
        have := (rB ℂ L x {0}).add_mem ha hb
        simpa [add_mul] using this
      zero_mem' := by simpa using (rB ℂ L x {0}).zero_mem
      smul_mem' := by
        intro c b hb
        have := (rB ℂ L x {0}).mul_mem c.2 hb
        simpa [mul_assoc] using this }
  have h𝔞 : ∀ e : fib ℂ L x, ∃ b ∈ 𝔞, e.1 b ≠ 0 := fun e => by
    obtain ⟨b, hb, hbv, hne, -⟩ := hg e
    exact ⟨⟨b, hb⟩, hbv, hne⟩
  obtain ⟨s, hs1, hs⟩ := nak x h 𝔞 (comax x h hred hCRT 𝔞 h𝔞)
  have hs' : algebraMap F L (s : F) * g ∈ rB ℂ L x {0} := hs
  have hone : ∀ e : fib ℂ L x, e.1 (FibFin.incl ℂ L x s) = 1 := fun e =>
    val_one x (e.1.comp (FibFin.incl ℂ L x)) (fun j => e.2 j) hs1
  have hval : ∀ e : fib ℂ L x, e.1 ⟨_, hs'⟩ = γ e := by
    intro e
    obtain ⟨b, hb, hbv, hne, heq⟩ := hg e
    have h1 : (⟨b, hb⟩ : rB ℂ L x {0}) * ⟨_, hs'⟩ = FibFin.incl ℂ L x s * ⟨b * g, hbv⟩ := by
      apply Subtype.ext
      change b * (algebraMap F L (s : F) * g) = algebraMap F L (s : F) * (b * g)
      ring
    have h2 := congrArg e.1 h1
    rw [map_mul, map_mul, hone, one_mul, heq] at h2
    exact mul_left_cancel₀ hne h2
  obtain ⟨e0⟩ := fib_nonempty x h hred
  have hev : ∀ f : rA ℂ x {0}, e0.1 (FibFin.incl ℂ L x f) = ρ f := by
    intro f
    obtain ⟨b, hb, hbv, hne, heq⟩ := hRes e0 f f.2
    have h1 : (⟨b * algebraMap F L f, hbv⟩ : rB ℂ L x {0}) = ⟨b, hb⟩ * FibFin.incl ℂ L x f := rfl
    rw [h1, map_mul] at heq
    exact mul_left_cancel₀ hne heq
  have htr : Algebra.trace F L (algebraMap F L (s : F) * g) = (s : F) * Algebra.trace F L g := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have h3 : ρ ((s : F) * Algebra.trace F L g) = ρ (Algebra.trace F L g) := by
    have h4 := hev (s * ⟨_, ht⟩)
    rw [map_mul, map_mul, hone e0, one_mul, hev] at h4
    exact h4.symm
  rw [← h3, ← htr]
  exact (hRT ⟨_, hs'⟩).trans (finsum_congr hval)

end UpperTheory.Gal.productCup_of_system.PartialTraceValue

end

/- English proof (translation)
Introduce `hRT hRes hCRT _ F L _ _ _ _ _ _ d x hc hred ρ hρ g γ hg ht`. Conclude with `PartialTraceValue.partialTrace_valuation_sum (xv x) hc hred ρ (hRT F L d x hc hred ρ hρ) (fun e f hf => hRes F L d x hc ρ hρ e f hf) (hCRT F L d x hc).2 g γ hg ht`.
-/
theorem UpperTheory.Gal.productCup_of_system.trVal_of :
    ResidueOfTraceIsFiberSum → ResVal → CRT → ValBasic → TrVal := by
  intro hRT hRes hCRT _ F L _ _ _ _ _ _ d x hc hred ρ hρ g γ hg ht
  exact PartialTraceValue.partialTrace_valuation_sum (xv x) hc hred ρ (hRT F L d x hc hred ρ hρ)
    (fun e f hf => hRes F L d x hc ρ hρ e f hf) (hCRT F L d x hc).2 g γ hg ht
