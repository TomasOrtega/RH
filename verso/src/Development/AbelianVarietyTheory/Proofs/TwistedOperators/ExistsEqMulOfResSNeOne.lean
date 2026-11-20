import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx GlobalTheory.Chain
open IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemRes

/- English proof (translation)
Establish `hm : I ∈ nonZeroDivisors (Ideal (𝓞 E))` using `mem_nonZeroDivisors_of_ne_zero hI`. Use `⟨Fintype.card (ClassGroup (𝓞 E)), Fintype.card_pos, ?_⟩` and prove the remaining obligations. Establish `h1 : ClassGroup.mk0 (⟨I, hm⟩ ^ Fintype.card (ClassGroup (𝓞 E))) = 1`. Rewrite using `[map_pow, pow_card_eq_one]`. Establish `h2` using `(ClassGroup.mk0_eq_one_iff (pow_mem hm (Fintype.card (ClassGroup (𝓞 E))))).1 h1`.

Conclude with `⟨_, h2.span_singleton_generator.symm⟩`.
-/
theorem exists_pow_eq_span {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    ∃ h : ℕ, 0 < h ∧ ∃ x : 𝓞 E, I ^ h = Ideal.span {x} := by
  have hm : I ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero hI
  refine ⟨Fintype.card (ClassGroup (𝓞 E)), Fintype.card_pos, ?_⟩
  have h1 : ClassGroup.mk0 (⟨I, hm⟩ ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have h2 := (ClassGroup.mk0_eq_one_iff (pow_mem hm (Fintype.card (ClassGroup (𝓞 E))))).1 h1
  exact ⟨_, h2.span_singleton_generator.symm⟩

/- English proof (translation)
Use `P.isPrime` as an intermediate fact. Establish `h0 : Formalism.L2.DIV.resS F P ε = 0`. Establish `h1 : Formalism.L2.DIV.resS F P ε * (Formalism.L2.DIV.resS F P ε - 1) = 0`. Rewrite using `[mul_sub, ← map_mul, hε, mul_one, sub_self]`. Conclude with `(mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 h)`.

Establish `hm : ε ∈ Formalism.L2.DIV.idS F P.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `(map_eq_zero_iff _ (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS F P.asIdeal) (Formalism.L2.DIV.cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective).1 h0`. Take `⟨n, hn, x, hx⟩` from `exists_pow_eq_span P.asIdeal P.ne_bot`. Establish `hp` using `Ideal.pow_mem_pow hm n`.

Establish `hi : ε ^ n = ε`. Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hn.ne'`. Conclude with `IsIdempotentElem.pow_succ_eq m hε`. Rewrite `hp` using `[hi, Formalism.L2.DIV.idS, ← Ideal.map_pow, hx, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']`. Take `⟨s, hs⟩` from `hp`.

Use `⟨x, Ideal.pow_le_self hn.ne' (hx ▸ Ideal.mem_span_singleton_self x), ?_, s, hs.symm⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hx` using `[Ideal.span_singleton_eq_bot.2 rfl]`. Conclude with `P.ne_bot (pow_eq_zero_iff hn.ne' |>.1 hx)`.
-/
theorem exists_eq_mul_of_resS_ne_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Formalism.L2.DIV.Pl E) (ε : Formalism.L2.Herm.intAf F E) (hε : ε * ε = ε) (h : Formalism.L2.DIV.resS F P ε ≠ 1) :
    ∃ x ∈ P.asIdeal, x ≠ 0 ∧ ∃ s : Formalism.L2.Herm.intAf F E, ε = s * Formalism.L2.DIV.oToS F E x := by
  have := P.isPrime
  have h0 : Formalism.L2.DIV.resS F P ε = 0 := by
    have h1 : Formalism.L2.DIV.resS F P ε * (Formalism.L2.DIV.resS F P ε - 1) = 0 := by
      rw [mul_sub, ← map_mul, hε, mul_one, sub_self]
    exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 h)
  have hm : ε ∈ Formalism.L2.DIV.idS F P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS F P.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective).1 h0
  obtain ⟨n, hn, x, hx⟩ := exists_pow_eq_span P.asIdeal P.ne_bot
  have hp := Ideal.pow_mem_pow hm n
  have hi : ε ^ n = ε := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact IsIdempotentElem.pow_succ_eq m hε
  rw [hi, Formalism.L2.DIV.idS, ← Ideal.map_pow, hx, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hp
  obtain ⟨s, hs⟩ := hp
  refine ⟨x, Ideal.pow_le_self hn.ne' (hx ▸ Ideal.mem_span_singleton_self x), ?_, s, hs.symm⟩
  rintro rfl
  rw [Ideal.span_singleton_eq_bot.2 rfl] at hx
  exact P.ne_bot (pow_eq_zero_iff hn.ne' |>.1 hx)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D w) ∈ _`. Generalize the expression as in `finPart D w = z at hw`. Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, rfl⟩` from `hy`.

Conclude with `GlobalTheory.PlaceDatum.tmul_mem_int ⟨x, rfl⟩ ha`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`.

Consider the case `neg a _ ha => rw [map_neg]`. Conclude with `neg_mem ha`.
-/
theorem toEAf_mem_of_finPart {D : D7} {w : AE D} (hw : finPart D w ∈ intAE D) :
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  change Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D w) ∈ _
  generalize finPart D w = z at hw
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    exact GlobalTheory.PlaceDatum.tmul_mem_int ⟨x, rfl⟩ ha
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

/- English proof (translation)
Introduce `D e P he`. Establish `h1 : e * e = e` using `he.1.1`. Establish `hint : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, h1]))`. Use `⟨hint, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Take `⟨x, hxP, hx0, s, hs⟩` from `exists_eq_mul_of_resS_ne_one P ⟨toEAf D e, hint⟩ (Subtype.ext (by change toEAf D e * toEAf D e = toEAf D e; rw [← RingHom.map_mul, h1])) hne`. Establish `hs' : toEAf D e = (s : Formalism.IndefR.Datum.EAf D) * eToEAf D (x : D.host.E)` using `congrArg Subtype.val hs`. Use `(he.2 x hx0).1 hxP (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_)` and prove the remaining obligations. Establish `hx0' : (x : D.host.E) ≠ 0` using `fun h => hx0 (RingOfIntegers.coe_eq_zero_iff.1 h)`. Establish `h2 : toEAf D (incA D ((x : D.host.E)⁻¹)) = eToEAf D ((x : D.host.E)⁻¹)` using `rfl`.

Rewrite using `[RingHom.map_mul, h2, hs', mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ hx0', RingHom.map_one, mul_one]`. Conclude with `s.2`.
-/
theorem resS_idem_eq_one : ∀ (D : D7) (e : AE D) (P : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P →
    ∃ h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, Formalism.L2.DIV.resS D.host.F P ⟨toEAf D e, h⟩ = 1 := by
  intro D e P he
  have h1 : e * e = e := he.1.1
  have hint : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, h1]))
  refine ⟨hint, ?_⟩
  by_contra hne
  obtain ⟨x, hxP, hx0, s, hs⟩ := exists_eq_mul_of_resS_ne_one P ⟨toEAf D e, hint⟩
    (Subtype.ext (by change toEAf D e * toEAf D e = toEAf D e; rw [← RingHom.map_mul, h1])) hne
  have hs' : toEAf D e = (s : Formalism.IndefR.Datum.EAf D) * eToEAf D (x : D.host.E) := congrArg Subtype.val hs
  refine (he.2 x hx0).1 hxP (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_)
  have hx0' : (x : D.host.E) ≠ 0 := fun h => hx0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have h2 : toEAf D (incA D ((x : D.host.E)⁻¹)) = eToEAf D ((x : D.host.E)⁻¹) := rfl
  rw [RingHom.map_mul, h2, hs', mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ hx0', RingHom.map_one, mul_one]
  exact s.2

end GlobalTheory.IdemRes

end
