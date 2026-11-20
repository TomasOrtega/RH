import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Filter Topology

namespace GlobalTheory.ChainOnto.TameRes

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `h` using `Valued.isOpen_ball (P.adicCompletion E) 1`. Simplify `h` using `only [Valuation.restrict_lt_iff_lt_embedding, map_one]`.
-/
theorem isOpen_ltOne (P : HeightOneSpectrum (𝓞 E)) :
    IsOpen {z : P.adicCompletion E | Valued.v z < 1} := by
  have h := Valued.isOpen_ball (P.adicCompletion E) 1
  simpa only [Valuation.restrict_lt_iff_lt_embedding, map_one] using h

/- English proof (translation)
The claim follows from `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P k`.
-/
theorem val_alg (P : HeightOneSpectrum (𝓞 E)) (k : E) :
    Valued.v (algebraMap E (P.adicCompletion E) k) = P.valuation E k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P k

/- English proof (translation)
The claim follows from `le_antisymm (P.valuation_le_one s) (not_lt.mp fun h => hs ((P.valuation_lt_one_iff_mem s).mp h))`.
-/
theorem valuation_eq_one_of_not_mem (P : HeightOneSpectrum (𝓞 E)) (s : 𝓞 E) (hs : s ∉ P.asIdeal) :
    P.valuation E (algebraMap (𝓞 E) E s) = 1 :=
  le_antisymm (P.valuation_le_one s) (not_lt.mp fun h => hs ((P.valuation_lt_one_iff_mem s).mp h))

/- English proof (translation)
Establish `hv1 : PP.valuation D.host.E (k : D.host.E) = 1`. Establish `e : (k : D.host.E) = 1 + ((k : D.host.E) - 1)` using `by ring`. Establish `h1 : PP.valuation D.host.E ((k : D.host.E) - 1) < PP.valuation D.host.E 1` using `by rwa [map_one]`. Rewrite using `[e]`. Use `first`.

Consider the case `rw [Valuation.map_add_eq_of_lt_right _ h1, map_one]`. Consider the case `rw [Valuation.map_add_eq_of_lt_left _ h1, map_one]`. Consider the case `rw [add_comm, Valuation.map_add_eq_of_lt_right _ h1, map_one]`. Consider the case `rw [add_comm, Valuation.map_add_eq_of_lt_left _ h1, map_one]`. Take `⟨a, s, h⟩` from `PP.exists_primeCompl_mul_eq_of_integer (k : D.host.E) hv1.le`.

Establish `hs : (s : 𝓞 D.host.E) ∉ PP.asIdeal` using `s.2`. Establish `hsv` using `valuation_eq_one_of_not_mem PP _ hs`. Establish `hav : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E a) = 1`. Rewrite using `[← h, map_mul, hv1, hsv, one_mul]`. Establish `ha : a ∉ PP.asIdeal`.

Introduce `hm`. Establish `hlt : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E a) < 1` using `(PP.valuation_lt_one_iff_mem (K := D.host.E) a).mpr hm`. Conclude with `absurd hav (ne_of_lt hlt)`. Establish `hs0 : algebraMap (𝓞 D.host.E) D.host.E s ≠ 0` using `fun h0 => by`. Rewrite `hsv` using `[h0, map_zero]`.

Conclude with `zero_ne_one hsv`. Establish `ha0 : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0` using `fun h0 => by`. Rewrite `hav` using `[h0, map_zero]`. Conclude with `zero_ne_one hav`. Establish `hdiff : a - (s : 𝓞 D.host.E) ∈ PP.asIdeal`.

Apply `(PP.valuation_lt_one_iff_mem (K := D.host.E) _).mp` to reduce the goal to its premises. Use `show PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E (a - (s : 𝓞 D.host.E))) < 1`. Rewrite using `[map_sub, ← h, ← sub_one_mul, map_mul, hsv, mul_one]`. Conclude with `hk`. Use `haveI : PP.asIdeal.IsMaximal := PP.isMaximal`.

Establish `hms : (Ideal.Quotient.mk PP.asIdeal (s : 𝓞 D.host.E) : kP PP) ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hs`. Take `⟨b, hb⟩` from `Ideal.Quotient.exists_inv hms`. Set `u : (kP PP)ˣ` to `Units.mkOfMulEqOne _ b hb`.

Set `ka : D.host.Eˣ` to `Units.mk0 _ ha0`. Set `ks : D.host.Eˣ` to `Units.mk0 _ hs0`. Establish `e1 : c u = H.locK PP ks` using `hc (s : 𝓞 D.host.E) ks u rfl rfl`. Establish `e2 : c u = H.locK PP ka` using `hc a ka u rfl (Ideal.Quotient.eq.mpr hdiff).symm`. Establish `hk' : k = ka * ks⁻¹`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ka, ks]`. Rewrite using `[← h, mul_assoc, mul_inv_cancel₀ hs0, mul_one]`. Rewrite using `[hk', map_mul, map_inv, ← e1, ← e2, mul_inv_cancel]`.
-/
theorem locK_eq_one (D : D7) (H : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (c : (kP PP)ˣ →* ℂˣ)
    (hc : IsRes H PP c) (k : D.host.Eˣ) (hk : PP.valuation D.host.E ((k : D.host.E) - 1) < 1) :
    H.locK PP k = 1 := by
  have hv1 : PP.valuation D.host.E (k : D.host.E) = 1 := by
    have e : (k : D.host.E) = 1 + ((k : D.host.E) - 1) := by ring
    have h1 : PP.valuation D.host.E ((k : D.host.E) - 1) < PP.valuation D.host.E 1 := by rwa [map_one]
    rw [e]
    first
      | rw [Valuation.map_add_eq_of_lt_right _ h1, map_one]
      | rw [Valuation.map_add_eq_of_lt_left _ h1, map_one]
      | rw [add_comm, Valuation.map_add_eq_of_lt_right _ h1, map_one]
      | rw [add_comm, Valuation.map_add_eq_of_lt_left _ h1, map_one]
  obtain ⟨a, s, h⟩ := PP.exists_primeCompl_mul_eq_of_integer (k : D.host.E) hv1.le
  have hs : (s : 𝓞 D.host.E) ∉ PP.asIdeal := s.2
  have hsv := valuation_eq_one_of_not_mem PP _ hs
  have hav : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E a) = 1 := by
    rw [← h, map_mul, hv1, hsv, one_mul]
  have ha : a ∉ PP.asIdeal := by
    intro hm
    have hlt : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E a) < 1 :=
      (PP.valuation_lt_one_iff_mem (K := D.host.E) a).mpr hm
    exact absurd hav (ne_of_lt hlt)
  have hs0 : algebraMap (𝓞 D.host.E) D.host.E s ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hsv; exact zero_ne_one hsv
  have ha0 : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hav; exact zero_ne_one hav
  have hdiff : a - (s : 𝓞 D.host.E) ∈ PP.asIdeal := by
    apply (PP.valuation_lt_one_iff_mem (K := D.host.E) _).mp
    show PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E (a - (s : 𝓞 D.host.E))) < 1
    rw [map_sub, ← h, ← sub_one_mul, map_mul, hsv, mul_one]
    exact hk
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  have hms : (Ideal.Quotient.mk PP.asIdeal (s : 𝓞 D.host.E) : kP PP) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hs
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hms
  let u : (kP PP)ˣ := Units.mkOfMulEqOne _ b hb
  let ka : D.host.Eˣ := Units.mk0 _ ha0
  let ks : D.host.Eˣ := Units.mk0 _ hs0
  have e1 : c u = H.locK PP ks := hc (s : 𝓞 D.host.E) ks u rfl rfl
  have e2 : c u = H.locK PP ka := hc a ka u rfl (Ideal.Quotient.eq.mpr hdiff).symm
  have hk' : k = ka * ks⁻¹ := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ka, ks]
    rw [← h, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [hk', map_mul, map_inv, ← e1, ← e2, mul_inv_cancel]

/- English proof (translation)
Introduce `D H PP c hc`. Unfold `Formalism.L2.Host.HChar.TameAt Formalism.L2.Host.HChar.LevelLe`. Introduce `x _ hx1`. Assume the negation of the conclusion as `hne`. Establish `hcont : Continuous (H.loc PP)` using `H.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele PP)`.

Establish `hW : IsOpen {y : (PP.adicCompletion D.host.E)ˣ | H.loc PP y ≠ 1}` using `isOpen_ne_fun hcont continuous_const`. Take `⟨T, hT, hTe⟩` from `Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hW`. Establish `hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1`. Rewrite using `[← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)`. Establish `hxT : (x : PP.adicCompletion D.host.E) ∈ T ∩ {z | Valued.v (z - 1) < 1}`.

Use `⟨?_, lt_of_le_of_lt hx1 hlt⟩` and prove the remaining obligations. Establish `: x ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion D.host.E)ˣ)` using `by rw [hTe]; exact hne`. Conclude with `this`. Establish `hU : IsOpen (T ∩ {z : PP.adicCompletion D.host.E | Valued.v (z - 1) < 1})` using `hT.inter ((isOpen_ltOne PP).preimage (continuous_sub_right 1))`. Take `⟨k, hk⟩` from `(HeightOneSpectrum.denseRange_algebraMap D.host.E PP).exists_mem_open hU ⟨_, hxT⟩`.

Establish `hk1 : PP.valuation D.host.E (k - 1) < 1`. Rewrite using `[← val_alg, map_sub, map_one]`. Conclude with `hk.2`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hk1`. Establish `hloc` using `locK_eq_one D H PP c hc (Units.mk0 k hk0) hk1`. Establish `hmem : Formalism.L2.Host.atFin PP (Units.mk0 k hk0) ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion D.host.E)ˣ)` using `hk.1`. Rewrite `hmem` using `[hTe]`. Conclude with `hmem hloc`.
-/
theorem tameAt_of_isRes : ∀ (D : D7) (H : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ),
    IsRes H PP a → H.TameAt PP := by
  intro D H PP c hc
  unfold Formalism.L2.Host.HChar.TameAt Formalism.L2.Host.HChar.LevelLe
  intro x _ hx1
  by_contra hne
  have hcont : Continuous (H.loc PP) := H.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele PP)
  have hW : IsOpen {y : (PP.adicCompletion D.host.E)ˣ | H.loc PP y ≠ 1} := isOpen_ne_fun hcont continuous_const
  obtain ⟨T, hT, hTe⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hW
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hxT : (x : PP.adicCompletion D.host.E) ∈ T ∩ {z | Valued.v (z - 1) < 1} := by
    refine ⟨?_, lt_of_le_of_lt hx1 hlt⟩
    have : x ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion D.host.E)ˣ) := by rw [hTe]; exact hne
    exact this
  have hU : IsOpen (T ∩ {z : PP.adicCompletion D.host.E | Valued.v (z - 1) < 1}) :=
    hT.inter ((isOpen_ltOne PP).preimage (continuous_sub_right 1))
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap D.host.E PP).exists_mem_open hU ⟨_, hxT⟩
  have hk1 : PP.valuation D.host.E (k - 1) < 1 := by
    rw [← val_alg, map_sub, map_one]; exact hk.2
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk1
  have hloc := locK_eq_one D H PP c hc (Units.mk0 k hk0) hk1
  have hmem : Formalism.L2.Host.atFin PP (Units.mk0 k hk0) ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion D.host.E)ˣ) := hk.1
  rw [hTe] at hmem
  exact hmem hloc

end GlobalTheory.ChainOnto.TameRes
