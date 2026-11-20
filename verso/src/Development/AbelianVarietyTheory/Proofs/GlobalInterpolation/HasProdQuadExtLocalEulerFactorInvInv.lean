import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSubConjNotMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotIsFieldAdicCompletionTensorOfSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticUnramifiedIffInertOrSplit
import Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree

noncomputable section

namespace GlobalTheory.EtaEulerProduct

open scoped TensorProduct Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex GlobalTheory.SelfDualLatticeCompare

open private euler_factor_log_bound partial_sums_log_euler_factor_le from Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

open scoped TensorProduct Pointwise in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [StarRing E] in
/- English proof (translation)
Establish `hfin : Module.finrank F E = 2` using `h.2.2.1`. Establish `hne` using `_root_.GlobalTheory.UnramConjUnit.conj_ne_id h`. Establish `hbij : Function.Bijective σ` using `⟨σ.injective, σ.toLinearMap.injective_iff_surjective.mp σ.injective⟩`. Set `τ : Gal(E/F)` to `AlgEquiv.ofBijective σ hbij`. Establish `hτ : ∀ x, τ x = σ x` using `fun x => rfl`.

Establish `hτ1 : τ ≠ 1`. Introduce `h1`. Apply `hne` to reduce the goal to its premises. Introduce `e`. Use `congrArg (fun g : Gal(E/F) => g e) h1` as an intermediate fact.

Simplify `this` using `[hτ]`. Establish `hle : Nat.card Gal(E/F) ≤ 2`. Rewrite using `[Nat.card_eq_fintype_card, ← hfin]`. Conclude with `AlgEquiv.card_le`. Establish `hge : 2 ≤ Nat.card Gal(E/F)` using `Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨τ, 1, hτ1⟩⟩`.

Establish `hc : Nat.card Gal(E/F) = 2` using `le_antisymm hle hge`. Conclude with `⟨IsGalois.of_card_aut_eq_finrank F E (by rw [hc, hfin]), hc, τ, hτ1, hτ⟩`.
-/
private theorem isGalois_card_two_of_isCMExt {σ : E →ₐ[F] E} (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) :
    IsGalois F E ∧ Nat.card Gal(E/F) = 2 ∧ ∃ τ : Gal(E/F), τ ≠ 1 ∧ ∀ x, τ x = σ x := by
  have hfin : Module.finrank F E = 2 := h.2.2.1
  have hne := _root_.GlobalTheory.UnramConjUnit.conj_ne_id h
  have hbij : Function.Bijective σ :=
    ⟨σ.injective, σ.toLinearMap.injective_iff_surjective.mp σ.injective⟩
  let τ : Gal(E/F) := AlgEquiv.ofBijective σ hbij
  have hτ : ∀ x, τ x = σ x := fun x => rfl
  have hτ1 : τ ≠ 1 := by
    intro h1; apply hne; intro e
    have := congrArg (fun g : Gal(E/F) => g e) h1
    simpa [hτ] using this
  have hle : Nat.card Gal(E/F) ≤ 2 := by
    rw [Nat.card_eq_fintype_card, ← hfin]; exact AlgEquiv.card_le
  have hge : 2 ≤ Nat.card Gal(E/F) :=
    Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨τ, 1, hτ1⟩⟩
  have hc : Nat.card Gal(E/F) = 2 := le_antisymm hle hge
  exact ⟨IsGalois.of_card_aut_eq_finrank F E (by rw [hc, hfin]), hc, τ, hτ1, hτ⟩

open scoped TensorProduct Pointwise in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [StarRing E] in
/- English proof (translation)
Rewrite `hf` using `[Ideal.inertiaDeg_eq_of_isMaximal p P]`. Use `letI := Ideal.Quotient.field p`. Establish `htop` using `Subalgebra.bot_eq_top_of_finrank_eq_one hf`. Establish `hx : Ideal.Quotient.mk P θ ∈ (⊥ : Subalgebra (𝓞 F ⧸ p) (𝓞 E ⧸ P))` using `htop ▸ Algebra.mem_top`. Take `⟨a, ha⟩` from `Algebra.mem_bot.mp hx`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq, ← ha]`. Both sides reduce to the same expression.
-/
private theorem exists_sub_algebraMap_mem_of_inertiaDeg_eq_one (p : Ideal (𝓞 F)) [p.IsMaximal]
    (P : Ideal (𝓞 E)) [P.IsMaximal] [P.LiesOver p]
    (hf : P.inertiaDeg (𝓞 F) = 1) (θ : 𝓞 E) : ∃ a : 𝓞 F, θ - algebraMap (𝓞 F) (𝓞 E) a ∈ P := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal p P] at hf
  letI := Ideal.Quotient.field p
  have htop := Subalgebra.bot_eq_top_of_finrank_eq_one hf
  have hx : Ideal.Quotient.mk P θ ∈ (⊥ : Subalgebra (𝓞 F ⧸ p) (𝓞 E ⧸ P)) :=
    htop ▸ Algebra.mem_top
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq, ← ha]
  rfl

open scoped TensorProduct Pointwise in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [StarRing E] in
/- English proof (translation)
Unfold `_root_.Formalism.HermitianLatticesTheory.conjIdeal`. Rewrite using `[Ideal.pointwise_smul_def, Ideal.map]`. Use `congr 1`. Use extensionality with `r`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs', hr⟩`. Use `⟨s, hs', ?_⟩` and prove the remaining obligations. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show _ = (algebraMap (𝓞 E) E) r`.

Rewrite using `[hr, hs]`. Both sides reduce to the same expression. Introduce and unpack `⟨s, hs', rfl⟩`. Use `⟨s, hs', ?_⟩` and prove the remaining obligations. Use `show ((τ • s : 𝓞 E) : E) = _`.

Rewrite using `[hs]`. Both sides reduce to the same expression.
-/
private theorem conjIdeal_eq_smul_of_star_eq (τ : Gal(E/F)) (hs : ∀ x : E, star x = τ x)
    (P : Ideal (𝓞 E)) : _root_.Formalism.HermitianLatticesTheory.conjIdeal (K := E) P = τ • P := by
  unfold _root_.Formalism.HermitianLatticesTheory.conjIdeal
  rw [Ideal.pointwise_smul_def, Ideal.map]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨s, hs', hr⟩
    refine ⟨s, hs', ?_⟩
    apply RingOfIntegers.ext
    show _ = (algebraMap (𝓞 E) E) r
    rw [hr, hs]; rfl
  · rintro ⟨s, hs', rfl⟩
    refine ⟨s, hs', ?_⟩
    show ((τ • s : 𝓞 E) : E) = _
    rw [hs]; rfl

open scoped TensorProduct Pointwise in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [StarRing E] in

/- English proof (translation)
Take `⟨hG, hc, τ, hτ1, hτ⟩` from `isGalois_card_two_of_isCMExt h`. Establish `hfin : Module.finrank F E = 2` using `h.2.2.1`. Establish `hsτ : ∀ x : E, star x = τ x` using `fun x => (hs x).trans (hτ x).symm`. Use `set p := v.asIdeal with hp`. Use `haveI : p.IsMaximal := v.isMaximal`.

Establish `hcount` using `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p (𝓞 E) Gal(E/F)`. Rewrite `hcount` using `[hc]`. Take `⟨P, hP⟩ : (p.primesOver (𝓞 E)).Nonempty` from `Set.Nonempty.of_subtype`. Use `haveI : P.IsPrime := hP.1`. Use `haveI : P.LiesOver p := hP.2`.

Use `haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p`. Establish `he` using `Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(E/F)`. Establish `hf` using `Ideal.inertiaDegIn_eq_inertiaDeg p P Gal(E/F)`. Establish `hfix : (p.primesOver (𝓞 E)).ncard = 1 → ∀ g : Gal(E/F), g • P = P`. Introduce `h1 g`.

Take `⟨Q, hQ⟩` from `Set.ncard_eq_one.mp h1`. Establish `h1 : g • P ∈ p.primesOver (𝓞 E)` using `⟨inferInstance, inferInstance⟩`. Rewrite `h1`, `hP` using `[hQ]`. Rewrite using `[Set.mem_singleton_iff.mp h1, Set.mem_singleton_iff.mp hP]`. Establish `hdvd : p.ramificationIdxIn (𝓞 E) * p.inertiaDegIn (𝓞 E) ∣ 2` using `Dvd.intro_left _ hcount`.

Establish `he1 : p.ramificationIdxIn (𝓞 E) = 1`. Assume the negation of the conclusion as `hne`. Break down `(Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2` into its components or cases. Conclude with `hne (Nat.eq_one_of_mul_eq_one_right h1)`. Establish `hn : (p.primesOver (𝓞 E)).ncard = 1` using `by rw [h2] at hcount; omega`.

Establish `hed : p.ramificationIdxIn (𝓞 E) ∣ 2` using `Dvd.intro _ h2`. Establish `he2 : p.ramificationIdxIn (𝓞 E) = 2`. Break down `(Nat.dvd_prime Nat.prime_two).mp hed with h | h` into its components or cases. Conclude with `absurd h hne`. Conclude with `h`.

Establish `hf1 : P.inertiaDeg (𝓞 F) = 1` using `by rw [← hf]; rw [he2] at h2; omega`. Take `⟨θ, t, ht, hθ⟩` from `hE.2.2 P inferInstance`. Take `⟨a, ha⟩` from `exists_sub_algebraMap_mem_of_inertiaDeg_eq_one p P hf1 θ`. Establish `htτ : t = τ • θ`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Use `show (algebraMap (𝓞 E) E) t = _`. Rewrite using `[ht, hsτ]`. Both sides reduce to the same expression. Establish `hfixa : τ • algebraMap (𝓞 F) (𝓞 E) a = algebraMap (𝓞 F) (𝓞 E) a`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Use `show τ ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) = _`. Conclude with `τ.commutes' _ |>.trans rfl`. Establish `hmem : τ • (θ - algebraMap (𝓞 F) (𝓞 E) a) ∈ τ • P` using `Ideal.smul_mem_pointwise_smul _ _ _ ha`. Rewrite `hmem` using `[hfix hn τ, smul_sub, hfixa, ← htτ]`. Apply `hθ` to reduce the goal to its premises.

Use `sub_mem ha hmem` as an intermediate fact. Simplify using `using this`. Establish `hunr : ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal`. Introduce `w hw`. Rewrite using `[Algebra.isUnramifiedAt_iff_of_isDedekindDomain]`.

Rewrite using `[← Ideal.ramificationIdxIn_eq_ramificationIdx p w.asIdeal Gal(E/F)]`. Conclude with `he1`. Establish `hio` using `(_root_.GlobalTheory.quadratic_unramified_iff_inert_or_split F E hfin v).mp hunr`. Rewrite `hcount` using `[he1, one_mul]`. Establish `hnorm : ∀ Q ∈ p.primesOver (𝓞 E), Ideal.absNorm Q = Ideal.absNorm p ^ p.inertiaDegIn (𝓞 E)`.

Introduce `Q hQ`. Use `haveI : Q.IsPrime := hQ.1`. Use `haveI : Q.LiesOver p := hQ.2`. Rewrite using `[Ideal.inertiaDegIn_eq_inertiaDeg p Q Gal(E/F), Ideal.absNorm_pow_inertiaDeg p Q]`. Establish `hdvd2 : (p.primesOver (𝓞 E)).ncard ∣ 2` using `Dvd.intro _ hcount`.

Break down `(Nat.dvd_prime Nat.prime_two).mp hdvd2 with hn | hn` into its components or cases. Use `left`. Establish `hf2 : p.inertiaDegIn (𝓞 E) = 2` using `by rw [hn] at hcount; omega`. Establish `hprime : (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal).IsPrime`. Break down `hio with h' | h'` into its components or cases.

Conclude with `h'`. Rewrite `h'` using `[← hp, hn]`. Use linear arithmetic over natural numbers and integers. Use `⟨_root_.GlobalTheory.InertField.isField_of_inert F E hfin v hprime, hn, fun Q hQ => ?_⟩` and prove the remaining obligations. Use `haveI : Q.IsPrime := hQ.1`.

Use `haveI : Q.LiesOver p := hQ.2`. Use `⟨?_, by rw [hnorm Q hQ, hf2]⟩` and prove the remaining obligations. Rewrite using `[conjIdeal_eq_smul_of_star_eq τ hsτ]`. Take `⟨R, hR⟩` from `Set.ncard_eq_one.mp hn`. Establish `h1 : τ • Q ∈ p.primesOver (𝓞 E)` using `⟨inferInstance, inferInstance⟩`.

Rewrite `h1`, `hQ` using `[hR]`. Rewrite using `[Set.mem_singleton_iff.mp h1, Set.mem_singleton_iff.mp hQ]`. Use `right`. Establish `hf1 : p.inertiaDegIn (𝓞 E) = 1` using `by rw [hn] at hcount; omega`. Use `⟨_root_.GlobalTheory.SplitPlace.not_isField_of_split F E hfin v hn, hn, fun Q hQ => ?_⟩` and prove the remaining obligations.

Use `haveI : Q.IsPrime := hQ.1`. Use `haveI : Q.LiesOver p := hQ.2`. Use `⟨?_, by rw [hnorm Q hQ, hf1, pow_one]⟩` and prove the remaining obligations. Rewrite using `[conjIdeal_eq_smul_of_star_eq τ hsτ]`. Introduce `hQτ`.

Take `⟨Q₁, Q₂, hne, hQ12⟩` from `Set.ncard_eq_two.mp hn`. Establish `hall : ∀ R ∈ p.primesOver (𝓞 E), R = Q`. Introduce `R hR`. Use `haveI : R.IsPrime := hR.1`. Use `haveI : R.LiesOver p := hR.2`.

Take `⟨g, hg⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup p Q R Gal(E/F)`. Take `⟨x, y, hxy, huniv⟩` from `Nat.card_eq_two_iff.mp hc`. Establish `hg' : g = 1 ∨ g = τ`. Establish `hgm : g ∈ ({x, y} : Set Gal(E/F))` using `huniv ▸ Set.mem_univ g`. Establish `h1m : (1 : Gal(E/F)) ∈ ({x, y} : Set Gal(E/F))` using `huniv ▸ Set.mem_univ 1`.

Establish `hτm : τ ∈ ({x, y} : Set Gal(E/F))` using `huniv ▸ Set.mem_univ τ`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgm h1m hτm`. Apply the tactic sequence `rcases hgm with rfl | rfl <;> rcases h1m with h1 | h1 <;> rcases hτm with h2 | h2 <;> first`. Consider the case `exact Or.inl h1.symm`. Consider the case `exact Or.inr h2.symm`.

Consider the case `exact absurd (h1.trans h2.symm) (Ne.symm hτ1)`. Break down `hg' with rfl | rfl` into its components or cases. Rewrite using `[← hg, one_smul]`. Rewrite using `[← hg, hQτ]`. Establish `h1` using `hall Q₁ (hQ12 ▸ Set.mem_insert _ _)`.

Establish `h2` using `hall Q₂ (hQ12 ▸ Set.mem_insert_of_mem _ rfl)`. Conclude with `hne (h1.trans h2.symm)`.
-/
theorem _root_.GlobalTheory.EtaEulerProduct.inert_or_split {σ : E →ₐ[F] E} (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ)
    (hs : ∀ x : E, star x = σ x) (hE : _root_.Formalism.HermitianLatticesTheory.IsCMUnram E) (v : HeightOneSpectrum (𝓞 F)) :
    (IsField (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) ∧ (v.asIdeal.primesOver (𝓞 E)).ncard = 1 ∧
      ∀ P ∈ v.asIdeal.primesOver (𝓞 E), _root_.Formalism.HermitianLatticesTheory.conjIdeal (K := E) P = P ∧
        Ideal.absNorm P = Ideal.absNorm v.asIdeal ^ 2) ∨
    (¬ IsField (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) ∧ (v.asIdeal.primesOver (𝓞 E)).ncard = 2 ∧
      ∀ P ∈ v.asIdeal.primesOver (𝓞 E), _root_.Formalism.HermitianLatticesTheory.conjIdeal (K := E) P ≠ P ∧
        Ideal.absNorm P = Ideal.absNorm v.asIdeal) := by
  obtain ⟨hG, hc, τ, hτ1, hτ⟩ := isGalois_card_two_of_isCMExt h
  have hfin : Module.finrank F E = 2 := h.2.2.1
  have hsτ : ∀ x : E, star x = τ x := fun x => (hs x).trans (hτ x).symm
  set p := v.asIdeal with hp
  haveI : p.IsMaximal := v.isMaximal
  have hcount := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p (𝓞 E) Gal(E/F)
  rw [hc] at hcount
  obtain ⟨P, hP⟩ : (p.primesOver (𝓞 E)).Nonempty := Set.Nonempty.of_subtype
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver p := hP.2
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p
  have he := Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(E/F)
  have hf := Ideal.inertiaDegIn_eq_inertiaDeg p P Gal(E/F)
  have hfix : (p.primesOver (𝓞 E)).ncard = 1 → ∀ g : Gal(E/F), g • P = P := by
    intro h1 g
    obtain ⟨Q, hQ⟩ := Set.ncard_eq_one.mp h1
    have h1 : g • P ∈ p.primesOver (𝓞 E) := ⟨inferInstance, inferInstance⟩
    rw [hQ] at h1 hP
    rw [Set.mem_singleton_iff.mp h1, Set.mem_singleton_iff.mp hP]
  have hdvd : p.ramificationIdxIn (𝓞 E) * p.inertiaDegIn (𝓞 E) ∣ 2 := Dvd.intro_left _ hcount
  have he1 : p.ramificationIdxIn (𝓞 E) = 1 := by
    by_contra hne
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact hne (Nat.eq_one_of_mul_eq_one_right h1)
    · have hn : (p.primesOver (𝓞 E)).ncard = 1 := by rw [h2] at hcount; omega
      have hed : p.ramificationIdxIn (𝓞 E) ∣ 2 := Dvd.intro _ h2
      have he2 : p.ramificationIdxIn (𝓞 E) = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hed with h | h
        · exact absurd h hne
        · exact h
      have hf1 : P.inertiaDeg (𝓞 F) = 1 := by rw [← hf]; rw [he2] at h2; omega
      obtain ⟨θ, t, ht, hθ⟩ := hE.2.2 P inferInstance
      obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_of_inertiaDeg_eq_one p P hf1 θ
      have htτ : t = τ • θ := by
        apply RingOfIntegers.ext
        show (algebraMap (𝓞 E) E) t = _
        rw [ht, hsτ]; rfl
      have hfixa : τ • algebraMap (𝓞 F) (𝓞 E) a = algebraMap (𝓞 F) (𝓞 E) a := by
        apply RingOfIntegers.ext
        show τ ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) = _
        exact τ.commutes' _ |>.trans rfl
      have hmem : τ • (θ - algebraMap (𝓞 F) (𝓞 E) a) ∈ τ • P :=
        Ideal.smul_mem_pointwise_smul _ _ _ ha
      rw [hfix hn τ, smul_sub, hfixa, ← htτ] at hmem
      apply hθ
      have := sub_mem ha hmem
      simpa using this
  have hunr : ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
      Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := by
    intro w hw
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx p w.asIdeal Gal(E/F)]
    exact he1
  have hio := (_root_.GlobalTheory.quadratic_unramified_iff_inert_or_split F E hfin v).mp hunr
  rw [he1, one_mul] at hcount
  have hnorm : ∀ Q ∈ p.primesOver (𝓞 E),
      Ideal.absNorm Q = Ideal.absNorm p ^ p.inertiaDegIn (𝓞 E) := by
    intro Q hQ
    haveI : Q.IsPrime := hQ.1
    haveI : Q.LiesOver p := hQ.2
    rw [Ideal.inertiaDegIn_eq_inertiaDeg p Q Gal(E/F), Ideal.absNorm_pow_inertiaDeg p Q]
  have hdvd2 : (p.primesOver (𝓞 E)).ncard ∣ 2 := Dvd.intro _ hcount
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with hn | hn
  · left
    have hf2 : p.inertiaDegIn (𝓞 E) = 2 := by rw [hn] at hcount; omega
    have hprime : (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal).IsPrime := by
      rcases hio with h' | h'
      · exact h'
      · rw [← hp, hn] at h'; omega
    refine ⟨_root_.GlobalTheory.InertField.isField_of_inert F E hfin v hprime, hn, fun Q hQ => ?_⟩
    haveI : Q.IsPrime := hQ.1
    haveI : Q.LiesOver p := hQ.2
    refine ⟨?_, by rw [hnorm Q hQ, hf2]⟩
    rw [conjIdeal_eq_smul_of_star_eq τ hsτ]
    obtain ⟨R, hR⟩ := Set.ncard_eq_one.mp hn
    have h1 : τ • Q ∈ p.primesOver (𝓞 E) := ⟨inferInstance, inferInstance⟩
    rw [hR] at h1 hQ
    rw [Set.mem_singleton_iff.mp h1, Set.mem_singleton_iff.mp hQ]
  · right
    have hf1 : p.inertiaDegIn (𝓞 E) = 1 := by rw [hn] at hcount; omega
    refine ⟨_root_.GlobalTheory.SplitPlace.not_isField_of_split F E hfin v hn, hn, fun Q hQ => ?_⟩
    haveI : Q.IsPrime := hQ.1
    haveI : Q.LiesOver p := hQ.2
    refine ⟨?_, by rw [hnorm Q hQ, hf1, pow_one]⟩
    rw [conjIdeal_eq_smul_of_star_eq τ hsτ]
    intro hQτ
    obtain ⟨Q₁, Q₂, hne, hQ12⟩ := Set.ncard_eq_two.mp hn
    have hall : ∀ R ∈ p.primesOver (𝓞 E), R = Q := by
      intro R hR
      haveI : R.IsPrime := hR.1
      haveI : R.LiesOver p := hR.2
      obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p Q R Gal(E/F)
      obtain ⟨x, y, hxy, huniv⟩ := Nat.card_eq_two_iff.mp hc
      have hg' : g = 1 ∨ g = τ := by
        have hgm : g ∈ ({x, y} : Set Gal(E/F)) := huniv ▸ Set.mem_univ g
        have h1m : (1 : Gal(E/F)) ∈ ({x, y} : Set Gal(E/F)) := huniv ▸ Set.mem_univ 1
        have hτm : τ ∈ ({x, y} : Set Gal(E/F)) := huniv ▸ Set.mem_univ τ
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgm h1m hτm
        rcases hgm with rfl | rfl <;> rcases h1m with h1 | h1 <;> rcases hτm with h2 | h2 <;>
          first
          | exact Or.inl h1.symm
          | exact Or.inr h2.symm
          | exact absurd (h1.trans h2.symm) (Ne.symm hτ1)
      rcases hg' with rfl | rfl
      · rw [← hg, one_smul]
      · rw [← hg, hQτ]
    have h1 := hall Q₁ (hQ12 ▸ Set.mem_insert _ _)
    have h2 := hall Q₂ (hQ12 ▸ Set.mem_insert_of_mem _ rfl)
    exact hne (h1.trans h2.symm)

def below (F : Type) [Field F] [NumberField F] [Algebra F E] (P : {P : Ideal (𝓞 E) // P.IsMaximal}) :
    HeightOneSpectrum (𝓞 F) :=
  HeightOneSpectrum.under (𝓞 F) (⟨P.1, P.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField P.2
    (RingOfIntegers.not_isField E)⟩ : HeightOneSpectrum (𝓞 E))

omit [StarRing E] in

def fibreEquiv (v : HeightOneSpectrum (𝓞 F)) :
    {P : {P : Ideal (𝓞 E) // P.IsMaximal} // below F P = v} ≃ v.asIdeal.primesOver (𝓞 E) where
  toFun P := ⟨P.1.1, P.1.2.isPrime, ⟨by obtain ⟨P, rfl⟩ := P; rfl⟩⟩
  invFun P := ⟨⟨P.1, by
      have := P.2.1
      have := P.2.2
      have := v.isMaximal
      exact Ideal.IsMaximal.of_liesOver_isMaximal P.1 v.asIdeal⟩,
    HeightOneSpectrum.ext P.2.2.over.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

open scoped TensorProduct Pointwise in
open NumberField IsDedekindDomain in
/- English proof (translation)
Use `haveI : (P.under ℤ).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P`. Establish `hne : P.under ℤ ≠ ⊥` using `Ideal.IsMaximal.ne_bot_of_isIntegral_int (Ideal.under ℤ P)`. Establish `hspan` using `Int.ideal_span_absNorm_eq_self (P.under ℤ)`. Establish `hprime : (Ideal.span {((Ideal.absNorm (P.under ℤ) : ℕ) : ℤ)}).IsPrime`. Rewrite using `[hspan]`.

Use `infer_instance`. Establish `h0 : ((Ideal.absNorm (P.under ℤ) : ℕ) : ℤ) ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← hspan, h0, Ideal.span_singleton_eq_bot.mpr rfl]`.

Use `(Ideal.span_singleton_prime h0).mp hprime` as an intermediate fact. Conclude with `Int.prime_iff_natAbs_prime.mp this`.
-/
private theorem absNorm_under_int_prime (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    [P.IsMaximal] : (Ideal.absNorm (P.under ℤ)).Prime := by
  haveI : (P.under ℤ).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hne : P.under ℤ ≠ ⊥ := Ideal.IsMaximal.ne_bot_of_isIntegral_int (Ideal.under ℤ P)
  have hspan := Int.ideal_span_absNorm_eq_self (P.under ℤ)
  have hprime : (Ideal.span {((Ideal.absNorm (P.under ℤ) : ℕ) : ℤ)}).IsPrime := by
    rw [hspan]; infer_instance
  have h0 : ((Ideal.absNorm (P.under ℤ) : ℕ) : ℤ) ≠ 0 := by
    intro h0; apply hne; rw [← hspan, h0, Ideal.span_singleton_eq_bot.mpr rfl]
  have := (Ideal.span_singleton_prime h0).mp hprime
  exact Int.prime_iff_natAbs_prime.mp this

open scoped TensorProduct Pointwise in
open NumberField IsDedekindDomain in
/- English proof (translation)
Establish `hP` using `Ideal.absNorm_pow_inertiaDeg (P.under ℤ) P`. Establish `hp` using `absNorm_under_int_prime K P`. Establish `hf : 0 < P.inertiaDeg ℤ` using `Ideal.inertiaDeg_pos P ℤ`. Rewrite using `[← hP]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem two_le_absNorm_of_isMaximal (K : Type) [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) [P.IsMaximal] : 2 ≤ Ideal.absNorm P := by
  have hP := Ideal.absNorm_pow_inertiaDeg (P.under ℤ) P
  have hp := absNorm_under_int_prime K P
  have hf : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos P ℤ
  rw [← hP]
  calc 2 ≤ Ideal.absNorm (P.under ℤ) := hp.two_le
    _ ≤ _ := Nat.le_self_pow hf.ne' _

open scoped TensorProduct Pointwise in
open NumberField IsDedekindDomain in
/- English proof (translation)
The claim follows from `|Real.log y| ≤ 2 * |y - 1| := by have hy0 : 0 < y := by linarith rcases le_or_gt 1 y with h1 | h1 · rw [abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg (by linarith)] linarith [Real.log_le_sub_one_of_pos hy0] · rw [abs_of_nonpos (Real.log_nonpos hy0.le h1.le), abs_of_neg (by li …`.
-/
private theorem abs_log_le_two_mul_abs_sub_one_of_half_le {y : ℝ} (hy : 1 / 2 ≤ y) :
    |Real.log y| ≤ 2 * |y - 1| := by
  have hy0 : 0 < y := by linarith
  rcases le_or_gt 1 y with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg (by linarith)]
    linarith [Real.log_le_sub_one_of_pos hy0]
  · rw [abs_of_nonpos (Real.log_nonpos hy0.le h1.le), abs_of_neg (by linarith)]
    have := Real.one_sub_inv_le_log_of_pos hy0
    have hinv : y⁻¹ ≤ 2 := by rw [inv_le_comm₀ hy0 (by norm_num)]; linarith
    have : 1 - y⁻¹ ≥ 2 * (y - 1) := by
      have : y⁻¹ * (1 - y) ≤ 2 * (1 - y) := mul_le_mul_of_nonneg_right hinv (by linarith)
      have h' : 1 - y⁻¹ = -(y⁻¹ * (1 - y)) := by field_simp; ring
      linarith
    linarith

open scoped TensorProduct Pointwise in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [StarRing E] in
/- English proof (translation)
The claim follows from `|Real.log (_root_.Formalism.HermitianLatticesTheory.eulerFac E M Q)| ≤ 2 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ)) := by haveI := v.isMaximal set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hqdef have hq : 2 ≤ q := by rw [hqdef]; exact_mod_cast two_le_absNorm_of_isMaximal F v. …`.
-/
private theorem eulerFac_hasProd_and_primesOver_card_le_two {σ : E →ₐ[F] E} (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ)
    (hs : ∀ x : E, star x = σ x) (hE : _root_.Formalism.HermitianLatticesTheory.IsCMUnram E) (M : ℕ) (hM : 2 ≤ M)
    (v : HeightOneSpectrum (𝓞 F)) :
    HasProd (fun Q : v.asIdeal.primesOver (𝓞 E) => _root_.Formalism.HermitianLatticesTheory.eulerFac E M Q.1)
        (_root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.eulerInv F E M v)⁻¹ ∧
      1 ≤ (v.asIdeal.primesOver (𝓞 E)).ncard ∧ (v.asIdeal.primesOver (𝓞 E)).ncard ≤ 2 ∧
      ∀ Q ∈ v.asIdeal.primesOver (𝓞 E), 0 < _root_.Formalism.HermitianLatticesTheory.eulerFac E M Q ∧
        |Real.log (_root_.Formalism.HermitianLatticesTheory.eulerFac E M Q)| ≤ 2 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ)) := by
  haveI := v.isMaximal
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hqdef
  have hq : 2 ≤ q := by
    rw [hqdef]; exact_mod_cast two_le_absNorm_of_isMaximal F v.asIdeal
  set x : ℝ := q ^ (-(M : ℤ)) with hxdef
  have hx0 : 0 < x := zpow_pos (by linarith) _
  have hq2 : q ^ (-(2 : ℝ)) = (q ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by linarith)]; norm_cast
  have hxle : x ≤ q ^ (-(2 : ℝ)) := by
    rw [hq2, hxdef, zpow_neg, zpow_natCast]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) hM)
  have hq4 : (q ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) (by nlinarith)
  have hx4 : x ≤ 1 / 4 := by linarith
  rcases _root_.GlobalTheory.EtaEulerProduct.inert_or_split h hs hE v with ⟨hF, hn, hQ⟩ | ⟨hF, hn, hQ⟩
  · set t : ℝ := (-1) ^ M * x with htdef
    have habs : |t| = x := by
      rw [htdef, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hx0]
    have ht : |t| ≤ 1 / 4 := habs ▸ hx4
    have hval : ∀ Q ∈ v.asIdeal.primesOver (𝓞 E), _root_.Formalism.HermitianLatticesTheory.eulerFac E M Q = (1 - t)⁻¹ := by
      intro Q hQm
      unfold _root_.Formalism.HermitianLatticesTheory.eulerFac
      rw [if_pos (hQ Q hQm).1, (hQ Q hQm).2]
      push_cast
      rw [Real.sqrt_sq (by positivity)]
    have heul : _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.eulerInv F E M v = 1 - t := by
      unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.eulerInv _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.etaV _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.resCard
      rw [if_pos hF]
    have hpos : 0 < 1 - t := by linarith [le_abs_self t]
    refine ⟨?_, by omega, by omega, fun Q hQm => ⟨by rw [hval Q hQm]; positivity, ?_⟩⟩
    · obtain ⟨Q₀, hQ₀⟩ := Set.ncard_eq_one.mp hn
      have hQ₀m : Q₀ ∈ v.asIdeal.primesOver (𝓞 E) := hQ₀ ▸ Set.mem_singleton Q₀
      rw [heul, ← hval Q₀ hQ₀m]
      rw [hQ₀, ← Finset.coe_singleton]
      convert Finset.hasProd ({Q₀} : Finset (Ideal (𝓞 E))) (fun Q => _root_.Formalism.HermitianLatticesTheory.eulerFac E M Q) using 1
      all_goals first | rfl | rw [Finset.prod_singleton]
    · rw [hval Q hQm, Real.log_inv, abs_neg]
      have := abs_log_le_two_mul_abs_sub_one_of_half_le (y := 1 - t) (by linarith [le_abs_self t])
      have h1 : |1 - t - 1| = |t| := by rw [sub_sub_cancel_left, abs_neg]
      rw [h1, habs] at this
      linarith
  · have hval : ∀ Q ∈ v.asIdeal.primesOver (𝓞 E), _root_.Formalism.HermitianLatticesTheory.eulerFac E M Q = (1 - x) ^ (-1 / 2 : ℝ) := by
      intro Q hQm
      unfold _root_.Formalism.HermitianLatticesTheory.eulerFac
      rw [if_neg (hQ Q hQm).1, (hQ Q hQm).2]
    have heul : _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.eulerInv F E M v = 1 - x := by
      unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.eulerInv _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.etaV _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.resCard
      rw [if_neg hF]; simp [hxdef, hqdef]
    have hpos : 0 < 1 - x := by linarith
    refine ⟨?_, by omega, by omega, fun Q hQm => ⟨by rw [hval Q hQm]; positivity, ?_⟩⟩
    · obtain ⟨Q₁, Q₂, hne, hS⟩ := Set.ncard_eq_two.mp hn
      have hQ₁ : Q₁ ∈ v.asIdeal.primesOver (𝓞 E) := hS ▸ Set.mem_insert _ _
      have hQ₂ : Q₂ ∈ v.asIdeal.primesOver (𝓞 E) := hS ▸ Set.mem_insert_of_mem _ rfl
      have hprod : _root_.Formalism.HermitianLatticesTheory.eulerFac E M Q₁ * _root_.Formalism.HermitianLatticesTheory.eulerFac E M Q₂ = (1 - x)⁻¹ := by
        rw [hval Q₁ hQ₁, hval Q₂ hQ₂, ← Real.rpow_add hpos]
        norm_num
        exact Real.rpow_neg_one _
      rw [heul, ← hprod, hS, ← Finset.coe_pair]
      convert Finset.hasProd ({Q₁, Q₂} : Finset (Ideal (𝓞 E))) (fun Q => _root_.Formalism.HermitianLatticesTheory.eulerFac E M Q) using 1
      all_goals first | rfl | rw [Finset.prod_pair hne]
    · rw [hval Q hQm, Real.log_rpow hpos, abs_mul]
      have := abs_log_le_two_mul_abs_sub_one_of_half_le (y := 1 - x) (by linarith)
      have h1 : |1 - x - 1| = x := by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hx0]
      rw [h1] at this
      have h2 : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
      rw [h2]
      linarith

open scoped TensorProduct Pointwise in
open NumberField IsDedekindDomain in
/- English proof (translation)
Establish `hP` using `Ideal.absNorm_pow_inertiaDeg (P.under ℤ) P`. Establish `hQ` using `Ideal.absNorm_pow_inertiaDeg (Q.under ℤ) Q`. Establish `hPp` using `absNorm_under_int_prime K P`. Establish `hQp` using `absNorm_under_int_prime K Q`. Establish `hfP : 0 < P.inertiaDeg ℤ` using `Ideal.inertiaDeg_pos P ℤ`.

Establish `hfQ : 0 < Q.inertiaDeg ℤ` using `Ideal.inertiaDeg_pos Q ℤ`. Establish `heq : Ideal.absNorm (P.under ℤ) = Ideal.absNorm (Q.under ℤ)`. Establish `h1` using `hPp.pow_minFac hfP.ne'`. Establish `h2` using `hQp.pow_minFac hfQ.ne'`. Rewrite using `[← h1, ← h2, hP, hQ, h]`.

Rewrite using `[← Int.ideal_span_absNorm_eq_self (P.under ℤ), ← Int.ideal_span_absNorm_eq_self (Q.under ℤ), heq]`.
-/
private theorem under_int_eq_of_absNorm_eq (K : Type) [Field K] [NumberField K]
    (P Q : Ideal (𝓞 K)) [P.IsMaximal] [Q.IsMaximal] (h : Ideal.absNorm P = Ideal.absNorm Q) :
    P.under ℤ = Q.under ℤ := by
  have hP := Ideal.absNorm_pow_inertiaDeg (P.under ℤ) P
  have hQ := Ideal.absNorm_pow_inertiaDeg (Q.under ℤ) Q
  have hPp := absNorm_under_int_prime K P
  have hQp := absNorm_under_int_prime K Q
  have hfP : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos P ℤ
  have hfQ : 0 < Q.inertiaDeg ℤ := Ideal.inertiaDeg_pos Q ℤ
  have heq : Ideal.absNorm (P.under ℤ) = Ideal.absNorm (Q.under ℤ) := by
    have h1 := hPp.pow_minFac hfP.ne'
    have h2 := hQp.pow_minFac hfQ.ne'
    rw [← h1, ← h2, hP, hQ, h]
  rw [← Int.ideal_span_absNorm_eq_self (P.under ℤ), ← Int.ideal_span_absNorm_eq_self (Q.under ℤ),
    heq]

open scoped TensorProduct Pointwise in
open NumberField IsDedekindDomain in
/- English proof (translation)
Use `set d := Module.finrank ℚ K`. Establish `hfib : ∀ n : ℕ, ∀ t : Finset {P : Ideal (𝓞 K) // P.IsMaximal}, (∀ P ∈ t, Ideal.absNorm P.1 = n) → t.card ≤ d`. Introduce `n t ht`. Break down `t.eq_empty_or_nonempty with rfl | ⟨P₀, hP₀⟩` into its components or cases. Simplify using the standard rewrite rules.

Use `haveI := P₀.2`. Use `haveI : (P₀.1.under ℤ).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P₀.1`. Establish `hne : P₀.1.under ℤ ≠ ⊥` using `Ideal.IsMaximal.ne_bot_of_isIntegral_int (Ideal.under ℤ P₀.1)`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.card_le_card` to reduce the goal to its premises.

Introduce `Q hQ`. Take `⟨Q, hQt, rfl⟩` from `Finset.mem_map.mp hQ`. Use `haveI := Q.2`. Establish `hlies : Q.1.LiesOver (P₀.1.under ℤ)` using `⟨?_⟩`. Conclude with `(IsDedekindDomain.mem_primesOverFinset_iff hne (𝓞 K)).mpr ⟨Q.2.isPrime, hlies⟩`.

Conclude with `(under_int_eq_of_absNorm_eq K Q.1 P₀.1 ((ht Q hQt).trans (ht P₀ hP₀).symm)).symm`. Use `_ ≤ d := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hne`. Set `e : {P : Ideal (𝓞 K) // P.IsMaximal} ≃ Σ n : ℕ, {P : {P : Ideal (𝓞 K) // P.IsMaximal} // Ideal.absNorm P.1 = n}` to `(Equiv.sigmaFiberEquiv (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Ideal.absNorm P.1)).symm`. Establish `hfin : ∀ n : ℕ, Finite {P : {P : Ideal (𝓞 K) // P.IsMaximal} // Ideal.absNorm P.1 = n}`. Introduce `n`.

Assume the negation of the conclusion as `hinf`. Rewrite `hinf` using `[not_finite_iff_infinite]`. Take `⟨t, ht⟩` from `Infinite.exists_subset_card_eq {P : {P : Ideal (𝓞 K) // P.IsMaximal} // Ideal.absNorm P.1 = n} (d + 1)`. Use `hfib n (t.map (Function.Embedding.subtype _)) (by` as an intermediate fact. Introduce `P hP`.

Take `⟨P, -, rfl⟩` from `Finset.mem_map.mp hP`. Conclude with `P.2)`. Rewrite `this` using `[Finset.card_map, ht]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← e.symm.summable_iff]`.

Use `(summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr ⟨fun n => by haveI := hfin n; exact Summable.of_finite, ?_⟩` and prove the remaining obligations. Use `Summable.of_nonneg_of_le (fun n => tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun n => ?_) ((Real.summable_nat_rpow.mpr (by linarith : -s < -1)).mul_left (d : ℝ))` and prove the remaining obligations. Use `haveI := hfin n`. Use `letI := Fintype.ofFinite {P : {P : Ideal (𝓞 K) // P.IsMaximal} // Ideal.absNorm P.1 = n}`. Establish `hconst : ∀ y : {P : {P : Ideal (𝓞 K) // P.IsMaximal} // Ideal.absNorm P.1 = n}, (Ideal.absNorm y.1.1 : ℝ) ^ (-s) = (n : ℝ) ^ (-s)` using `fun y => by rw [y.2]`.

Simplify using `only [e, Equiv.symm_symm, Equiv.sigmaFiberEquiv_apply]`. Rewrite using `[tsum_congr hconst, tsum_const, nsmul_eq_mul]`. Use `gcongr`. Establish `hc` using `hfib n (Finset.univ.map (Function.Embedding.subtype (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Ideal.absNorm P.1 = n))) (by`. Introduce `P hP`.

Take `⟨P, -, rfl⟩` from `Finset.mem_map.mp hP`. Conclude with `P.2)`. Rewrite `hc` using `[Finset.card_map, Finset.card_univ]`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `hc` after adjusting the coercions.
-/
private theorem summable_absNorm_maximal_rpow_neg (K : Type) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => (Ideal.absNorm P.1 : ℝ) ^ (-s)) := by
  set d := Module.finrank ℚ K
  have hfib : ∀ n : ℕ, ∀ t : Finset {P : Ideal (𝓞 K) // P.IsMaximal},
      (∀ P ∈ t, Ideal.absNorm P.1 = n) → t.card ≤ d := by
    intro n t ht
    rcases t.eq_empty_or_nonempty with rfl | ⟨P₀, hP₀⟩
    · simp
    haveI := P₀.2
    haveI : (P₀.1.under ℤ).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P₀.1
    have hne : P₀.1.under ℤ ≠ ⊥ := Ideal.IsMaximal.ne_bot_of_isIntegral_int (Ideal.under ℤ P₀.1)
    calc t.card = (t.map (Function.Embedding.subtype _)).card := (Finset.card_map _).symm
      _ ≤ (IsDedekindDomain.primesOverFinset (P₀.1.under ℤ) (𝓞 K)).card := by
        apply Finset.card_le_card
        intro Q hQ
        obtain ⟨Q, hQt, rfl⟩ := Finset.mem_map.mp hQ
        haveI := Q.2
        have hlies : Q.1.LiesOver (P₀.1.under ℤ) := ⟨?_⟩
        · exact (IsDedekindDomain.mem_primesOverFinset_iff hne (𝓞 K)).mpr ⟨Q.2.isPrime, hlies⟩
        exact (under_int_eq_of_absNorm_eq K Q.1 P₀.1 ((ht Q hQt).trans (ht P₀ hP₀).symm)).symm
      _ ≤ d := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hne
  let e : {P : Ideal (𝓞 K) // P.IsMaximal} ≃
      Σ n : ℕ, {P : {P : Ideal (𝓞 K) // P.IsMaximal} // Ideal.absNorm P.1 = n} :=
    (Equiv.sigmaFiberEquiv (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Ideal.absNorm P.1)).symm
  have hfin : ∀ n : ℕ, Finite {P : {P : Ideal (𝓞 K) // P.IsMaximal} // Ideal.absNorm P.1 = n} := by
    intro n
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    obtain ⟨t, ht⟩ := Infinite.exists_subset_card_eq
      {P : {P : Ideal (𝓞 K) // P.IsMaximal} // Ideal.absNorm P.1 = n} (d + 1)
    have := hfib n (t.map (Function.Embedding.subtype _)) (by
      intro P hP
      obtain ⟨P, -, rfl⟩ := Finset.mem_map.mp hP
      exact P.2)
    rw [Finset.card_map, ht] at this
    omega
  rw [← e.symm.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr ⟨fun n => by haveI := hfin n; exact Summable.of_finite, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun n => ?_) ((Real.summable_nat_rpow.mpr (by linarith : -s < -1)).mul_left (d : ℝ))
  haveI := hfin n
  letI := Fintype.ofFinite {P : {P : Ideal (𝓞 K) // P.IsMaximal} // Ideal.absNorm P.1 = n}
  have hconst : ∀ y : {P : {P : Ideal (𝓞 K) // P.IsMaximal} // Ideal.absNorm P.1 = n},
      (Ideal.absNorm y.1.1 : ℝ) ^ (-s) = (n : ℝ) ^ (-s) := fun y => by rw [y.2]
  simp only [e, Equiv.symm_symm, Equiv.sigmaFiberEquiv_apply]
  rw [tsum_congr hconst, tsum_const, nsmul_eq_mul]
  gcongr
  have hc := hfib n (Finset.univ.map (Function.Embedding.subtype
      (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Ideal.absNorm P.1 = n))) (by
    intro P hP
    obtain ⟨P, -, rfl⟩ := Finset.mem_map.mp hP
    exact P.2)
  rw [Finset.card_map, Finset.card_univ] at hc
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast hc

open scoped TensorProduct Pointwise in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [StarRing E] in

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ h hs hE M hM`. Use `set g : {P : Ideal (𝓞 E) // P.IsMaximal} → ℝ := fun P => _root_.Formalism.HermitianLatticesTheory.eulerFac E M P.1 with hg`. Set `e` to `Equiv.sigmaFiberEquiv (fun P : {P : Ideal (𝓞 E) // P.IsMaximal} => _root_.GlobalTheory.EtaEulerProduct.below F P)`. Establish `hmem : ∀ P : {P : Ideal (𝓞 E) // P.IsMaximal}, P.1 ∈ (_root_.GlobalTheory.EtaEulerProduct.below F P).asIdeal.primesOver (𝓞 E)` using `fun P => (_root_.GlobalTheory.EtaEulerProduct.fibreEquiv (_root_.GlobalTheory.EtaEulerProduct.below F P) ⟨P, rfl⟩).2`. Establish `hfib` using `fun v => eulerFac_hasProd_and_primesOver_card_le_two h hs hE M hM v`.

Establish `hgpos : ∀ P, 0 < g P` using `fun P => ((hfib _).2.2.2 P.1 (hmem P)).1`. Establish `hfin : ∀ v : HeightOneSpectrum (𝓞 F), Finite {P : {P : Ideal (𝓞 E) // P.IsMaximal} // _root_.GlobalTheory.EtaEulerProduct.below F P = v}`. Introduce `v`. Use `haveI : Finite (v.asIdeal.primesOver (𝓞 E)) := Set.finite_coe_iff.mpr (Set.finite_of_ncard_ne_zero (by have := (hfib v).2.1; omega))`. Conclude with `Finite.of_equiv _ (_root_.GlobalTheory.EtaEulerProduct.fibreEquiv v).symm`.

Establish `hsumF : Summable (fun v : HeightOneSpectrum (𝓞 F) => (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ)))`. Establish `hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 F) => (⟨v.asIdeal, v.isMaximal⟩ : {P : Ideal (𝓞 F) // P.IsMaximal}))`. Introduce `v w hvw`. Conclude with `HeightOneSpectrum.ext (congrArg Subtype.val hvw)`. Establish `h2` using `summable_absNorm_maximal_rpow_neg F (s := 2) (by norm_num)`.

Establish `h3` using `h2.comp_injective hinj`. Conclude with `h3`. Establish `hsum : Summable (fun P => Real.log (g P))`. Apply `Summable.of_abs` to reduce the goal to its premises. Rewrite using `[← e.summable_iff]`.

Use `(summable_sigma_of_nonneg (fun _ => abs_nonneg _)).mpr ⟨fun v => ?_, ?_⟩` and prove the remaining obligations. Use `haveI := hfin v`. Conclude with `Summable.of_finite`. Use `Summable.of_nonneg_of_le (fun v => tsum_nonneg fun _ => abs_nonneg _) (fun v => ?_) (hsumF.mul_left 4) haveI := hfin v` and prove the remaining obligations. Use `letI := Fintype.ofFinite {P : {P : Ideal (𝓞 E) // P.IsMaximal} // _root_.GlobalTheory.EtaEulerProduct.below F P = v}`.

Rewrite using `[tsum_fintype]`. Establish `hb : ∀ y : {P : {P : Ideal (𝓞 E) // P.IsMaximal} // _root_.GlobalTheory.EtaEulerProduct.below F P = v}, |Real.log (g y.1)| ≤ 2 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ))`. Introduce `y`. Establish `hm` using `hmem y.1`. Rewrite `hm` using `[y.2]`.

Conclude with `((hfib v).2.2.2 y.1.1 hm).2`. Establish `hcard : (Fintype.card {P : {P : Ideal (𝓞 E) // P.IsMaximal} // _root_.GlobalTheory.EtaEulerProduct.below F P = v} : ℝ) ≤ 2`. Rewrite using `[← Nat.card_eq_fintype_card, Nat.card_congr (_root_.GlobalTheory.EtaEulerProduct.fibreEquiv v), Nat.card_coe_set_eq]`. Conclude with `(hfib v).2.2.1` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Use `_ ≤ 2 * (2 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ))) := by gcongr`. Use `_ = 4 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ)) := by ring`. Take `⟨S, hS⟩` from `hsum`. Establish `hprod : HasProd g (Real.exp S)` using `by first`.

Consider the case `exact Real.hasProd_of_hasSum_log hgpos hS`. Consider the case `exact hasProd_of_hasSum_log (fun P => (hgpos P).ne') hS`. Establish `hval : _root_.Formalism.HermitianLatticesTheory.lValEta E M = Real.exp S`. Unfold `_root_.Formalism.HermitianLatticesTheory.lValEta`. Conclude with `hprod.tprod_eq`.

Use `⟨by rw [hval]; exact Real.exp_pos S, ?_⟩` and prove the remaining obligations. Rewrite using `[hval]`. Establish `hsig : HasProd (g ∘ e) (Real.exp S)` using `(e.hasProd_iff).mpr hprod`. Use `hsig.sigma (fun v => ?_)` and prove the remaining obligations. Use `(hfib v).1` as an intermediate fact.

Rewrite `this` using `[← (_root_.GlobalTheory.EtaEulerProduct.fibreEquiv v).hasProd_iff]`. Conclude with `this`.
-/
theorem _root_.GlobalTheory.EtaEulerProduct.hasProd_eulerInv_inv : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    (∀ x : E, star x = σ x) → _root_.Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ M : ℕ, 2 ≤ M →
    0 < _root_.Formalism.HermitianLatticesTheory.lValEta E M ∧
      HasProd (fun v => (_root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.eulerInv F E M v)⁻¹) (_root_.Formalism.HermitianLatticesTheory.lValEta E M) := by
  intro F E _ _ _ _ _ _ σ h hs hE M hM
  set g : {P : Ideal (𝓞 E) // P.IsMaximal} → ℝ := fun P => _root_.Formalism.HermitianLatticesTheory.eulerFac E M P.1 with hg
  let e := Equiv.sigmaFiberEquiv
    (fun P : {P : Ideal (𝓞 E) // P.IsMaximal} => _root_.GlobalTheory.EtaEulerProduct.below F P)
  have hmem : ∀ P : {P : Ideal (𝓞 E) // P.IsMaximal},
      P.1 ∈ (_root_.GlobalTheory.EtaEulerProduct.below F P).asIdeal.primesOver (𝓞 E) := fun P =>
    (_root_.GlobalTheory.EtaEulerProduct.fibreEquiv (_root_.GlobalTheory.EtaEulerProduct.below F P) ⟨P, rfl⟩).2
  have hfib := fun v => eulerFac_hasProd_and_primesOver_card_le_two h hs hE M hM v
  have hgpos : ∀ P, 0 < g P := fun P => ((hfib _).2.2.2 P.1 (hmem P)).1
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      Finite {P : {P : Ideal (𝓞 E) // P.IsMaximal} // _root_.GlobalTheory.EtaEulerProduct.below F P = v} := by
    intro v
    haveI : Finite (v.asIdeal.primesOver (𝓞 E)) :=
      Set.finite_coe_iff.mpr (Set.finite_of_ncard_ne_zero (by have := (hfib v).2.1; omega))
    exact Finite.of_equiv _ (_root_.GlobalTheory.EtaEulerProduct.fibreEquiv v).symm
  have hsumF : Summable (fun v : HeightOneSpectrum (𝓞 F) =>
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ))) := by
    have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 F) =>
        (⟨v.asIdeal, v.isMaximal⟩ : {P : Ideal (𝓞 F) // P.IsMaximal})) := by
      intro v w hvw
      exact HeightOneSpectrum.ext (congrArg Subtype.val hvw)
    have h2 := summable_absNorm_maximal_rpow_neg F (s := 2) (by norm_num)
    have h3 := h2.comp_injective hinj
    exact h3
  have hsum : Summable (fun P => Real.log (g P)) := by
    apply Summable.of_abs
    rw [← e.summable_iff]
    refine (summable_sigma_of_nonneg (fun _ => abs_nonneg _)).mpr ⟨fun v => ?_, ?_⟩
    · haveI := hfin v
      exact Summable.of_finite
    · refine Summable.of_nonneg_of_le (fun v => tsum_nonneg fun _ => abs_nonneg _) (fun v => ?_)
        (hsumF.mul_left 4)
      haveI := hfin v
      letI := Fintype.ofFinite
        {P : {P : Ideal (𝓞 E) // P.IsMaximal} // _root_.GlobalTheory.EtaEulerProduct.below F P = v}
      rw [tsum_fintype]
      have hb : ∀ y : {P : {P : Ideal (𝓞 E) // P.IsMaximal} // _root_.GlobalTheory.EtaEulerProduct.below F P = v},
          |Real.log (g y.1)| ≤ 2 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ)) := by
        intro y
        have hm := hmem y.1
        rw [y.2] at hm
        exact ((hfib v).2.2.2 y.1.1 hm).2
      have hcard : (Fintype.card {P : {P : Ideal (𝓞 E) // P.IsMaximal} //
          _root_.GlobalTheory.EtaEulerProduct.below F P = v} : ℝ) ≤ 2 := by
        rw [← Nat.card_eq_fintype_card, Nat.card_congr (_root_.GlobalTheory.EtaEulerProduct.fibreEquiv v),
          Nat.card_coe_set_eq]
        exact_mod_cast (hfib v).2.2.1
      calc ∑ y, |Real.log (g (e ⟨v, y⟩))|
          ≤ ∑ _y : {P : {P : Ideal (𝓞 E) // P.IsMaximal} // _root_.GlobalTheory.EtaEulerProduct.below F P = v},
            2 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ)) :=
            Finset.sum_le_sum fun y _ => hb y
        _ = Fintype.card {P : {P : Ideal (𝓞 E) // P.IsMaximal} //
              _root_.GlobalTheory.EtaEulerProduct.below F P = v} *
            (2 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ))) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ 2 * (2 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ))) := by
            gcongr
        _ = 4 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ)) := by ring
  obtain ⟨S, hS⟩ := hsum
  have hprod : HasProd g (Real.exp S) := by
    first
    | exact Real.hasProd_of_hasSum_log hgpos hS
    | exact hasProd_of_hasSum_log (fun P => (hgpos P).ne') hS
  have hval : _root_.Formalism.HermitianLatticesTheory.lValEta E M = Real.exp S := by
    unfold _root_.Formalism.HermitianLatticesTheory.lValEta
    exact hprod.tprod_eq
  refine ⟨by rw [hval]; exact Real.exp_pos S, ?_⟩
  rw [hval]
  have hsig : HasProd (g ∘ e) (Real.exp S) := (e.hasProd_iff).mpr hprod
  refine hsig.sigma (fun v => ?_)
  have := (hfib v).1
  rw [← (_root_.GlobalTheory.EtaEulerProduct.fibreEquiv v).hasProd_iff] at this
  exact this

end GlobalTheory.EtaEulerProduct
