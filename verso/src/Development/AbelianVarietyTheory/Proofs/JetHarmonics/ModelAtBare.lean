import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.UnifAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.UniformizationClosedSplit

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Proof.ModelAtPrimeToLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit
open scoped CategoryTheory.Obj

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨h.not_mem_M, fun hA => h ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩ : l.A ∣ l.M'` from `Nat.dvd_lcm_right _ _`. Rewrite using `[hk, Nat.cast_mul]`.

Conclude with `Ideal.mul_mem_right _ _ hA`. Introduce and unpack `⟨hM, hA⟩ h`. Take `⟨k, hk⟩ : l.M' ∣ l.M * l.A` from `Nat.lcm_dvd_mul _ _`. Establish `h2 : ((l.M : ℕ) : 𝓞 c.F) * ((l.A : ℕ) : 𝓞 c.F) ∈ la.asIdeal`. Rewrite using `[← Nat.cast_mul, hk, Nat.cast_mul]`.

Conclude with `Ideal.mul_mem_right _ _ h`. Conclude with `(la.isPrime.mem_or_mem h2).elim hM hA`.
-/
theorem primeToLevel_iff_and (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) :
    PrimeToLevel c la ↔ ((l.M : ℕ) : 𝓞 c.F) ∉ la.asIdeal ∧ ((l.A : ℕ) : 𝓞 c.F) ∉ la.asIdeal := by
  constructor
  · intro h
    refine ⟨h.not_mem_M, fun hA => h ?_⟩
    obtain ⟨k, hk⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hA
  · rintro ⟨hM, hA⟩ h
    obtain ⟨k, hk⟩ : l.M' ∣ l.M * l.A := Nat.lcm_dvd_mul _ _
    have h2 : ((l.M : ℕ) : 𝓞 c.F) * ((l.A : ℕ) : 𝓞 c.F) ∈ la.asIdeal := by
      rw [← Nat.cast_mul, hk, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ h
    exact (la.isPrime.mem_or_mem h2).elim hM hA

/- English proof (translation)
Unfold `PrimeToLevel Level.M'`. Rewrite using `[hA, Nat.lcm_one_right]`.
-/
theorem primeToLevel_iff (c : Coeff l) (hA : l.A = 1) (la : HeightOneSpectrum (𝓞 c.F)) :
    PrimeToLevel c la ↔ ((l.M : ℕ) : 𝓞 c.F) ∉ la.asIdeal := by
  unfold PrimeToLevel Level.M'
  rw [hA, Nat.lcm_one_right]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨O, i, β, b, Y, hb, h3⟩`. Conclude with `⟨O, i, β, Y, b, h3, RingHom.ext hb⟩`. Introduce and unpack `⟨O, i, β, Y, b, h3, hb⟩`. Conclude with `⟨O, i, β, b, Y, fun x => RingHom.congr_fun hb x, h3⟩`.
-/
theorem hasModel_iff (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) :
    HasModel Xo c T io ↔
      ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (Y : Model Xo c β) (b : O →+* T.V),
        Y.N3 ∧ (algebraMap T.V T.Fr).comp b = io.comp β := by
  constructor
  · rintro ⟨O, i, β, b, Y, hb, h3⟩
    exact ⟨O, i, β, Y, b, h3, RingHom.ext hb⟩
  · rintro ⟨O, i, β, Y, b, h3, hb⟩
    exact ⟨O, i, β, b, Y, fun x => RingHom.congr_fun hb x, h3⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨O, i, β, Y, hP, h⟩ T io e ho`. Take `⟨b, hb⟩` from `h T io e ho`. Conclude with `⟨O, i, β, b, Y, fun x => RingHom.congr_fun hb x, hP⟩`. Introduce `h`.

Take `⟨T₀, io₀, h₀, -, hu⟩` from `GlobalTheory.PlaceCompletion.exists_initial_completion c.F la`. Take `⟨O, i, β, b, Y, hb, hP⟩` from `h T₀ io₀ 1 h₀`. Establish `hb' : (algebraMap T₀.V T₀.Fr).comp b = io₀.comp β` using `RingHom.ext hb`. Use `⟨O, i, β, Y, hP, fun T io e ho => ?_⟩` and prove the remaining obligations. Take `⟨g, χ, -, h1, h2, -⟩` from `hu T io e ho`.

Use `⟨g.comp b, ?_⟩` and prove the remaining obligations. Rewrite using `[← RingHom.comp_assoc, ← h2, RingHom.comp_assoc, hb', ← RingHom.comp_assoc, h1]`.
-/
theorem uniform_iff (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F))
    (P : ∀ (O : Type) (_ : CommRing O) (β : O →+* c.F), Model Xo c β → Prop) :
    (∃ (O : Type) (i : CommRing O) (β : O →+* c.F) (Y : Model Xo c β), P O i β Y ∧
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
        ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = io.comp β) ↔
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
      ∃ (O : Type) (i : CommRing O) (β : O →+* c.F) (b : O →+* T.V) (Y : Model Xo c β),
        (∀ x : O, algebraMap T.V T.Fr (b x) = io (β x)) ∧ P O i β Y := by
  constructor
  · rintro ⟨O, i, β, Y, hP, h⟩ T io e ho
    obtain ⟨b, hb⟩ := h T io e ho
    exact ⟨O, i, β, b, Y, fun x => RingHom.congr_fun hb x, hP⟩
  · intro h
    obtain ⟨T₀, io₀, h₀, -, hu⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion c.F la
    obtain ⟨O, i, β, b, Y, hb, hP⟩ := h T₀ io₀ 1 h₀
    have hb' : (algebraMap T₀.V T₀.Fr).comp b = io₀.comp β := RingHom.ext hb
    refine ⟨O, i, β, Y, hP, fun T io e ho => ?_⟩
    obtain ⟨g, χ, -, h1, h2, -⟩ := hu T io e ho
    refine ⟨g.comp b, ?_⟩
    rw [← RingHom.comp_assoc, ← h2, RingHom.comp_assoc, hb', ← RingHom.comp_assoc, h1]

def HasModelPush (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) : Prop :=
  ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (b : O →+* T.V) (Y : Model Xo c β),
    (∀ x : O, algebraMap T.V T.Fr (b x) = io (β x)) ∧ Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L

/- English proof (translation)
Take `⟨O, i, β, b, Y, hb, h3, -⟩` from `h`. Conclude with `⟨O, i, β, b, Y, hb, h3⟩`.
-/
theorem HasModelPush.hasModel {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr}
    (h : HasModelPush Xo c T io) : HasModel Xo c T io := by
  obtain ⟨O, i, β, b, Y, hb, h3, -⟩ := h
  exact ⟨O, i, β, b, Y, hb, h3⟩

def ModelAtBare (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) : Prop :=
  ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (Y : Model Xo c β), Y.N3 ∧
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
      ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = io.comp β

/- English proof (translation)
Take `⟨O, i, β, Y, h3, -, hb⟩` from `h`. Conclude with `⟨O, i, β, Y, h3, hb⟩`.
-/
theorem modelAtBare_of_modelAtSt {Xo : Moduli Dw l} {c : Coeff l} {la : HeightOneSpectrum (𝓞 c.F)}
    (h : ModelAtSt Xo c la) : ModelAtBare Xo c la := by
  obtain ⟨O, i, β, Y, h3, -, hb⟩ := h
  exact ⟨O, i, β, Y, h3, hb⟩

/- English proof (translation)
Use `Iff.trans ?_ (uniform_iff Xo c la fun _ _ _ Y => Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨O, i, β, Y, h3, hP, hb⟩`. Conclude with `⟨O, i, β, Y, ⟨h3, hP⟩, hb⟩`. Introduce and unpack `⟨O, i, β, Y, ⟨h3, hP⟩, hb⟩`.

Conclude with `⟨O, i, β, Y, h3, hP, hb⟩`.
-/
theorem modelAtSt_place_iff (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) :
    ModelAtSt Xo c la ↔
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → HasModelPush Xo c T io := by
  refine Iff.trans ?_ (uniform_iff Xo c la fun _ _ _ Y => Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L)
  constructor
  · rintro ⟨O, i, β, Y, h3, hP, hb⟩
    exact ⟨O, i, β, Y, ⟨h3, hP⟩, hb⟩
  · rintro ⟨O, i, β, Y, ⟨h3, hP⟩, hb⟩
    exact ⟨O, i, β, Y, h3, hP, hb⟩

/- English proof (translation)
The claim follows from `uniform_iff Xo c la fun _ _ _ Y => Y.N3`.
-/
theorem modelAtBare_iff (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) :
    ModelAtBare Xo c la ↔
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → HasModel Xo c T io :=
  uniform_iff Xo c la fun _ _ _ Y => Y.N3

/- English proof (translation)
The claim follows from `forall_congr' fun la => forall_congr' fun _ => (modelAtBare_iff Xo c la).symm`.
-/
theorem modelAt_iff_uniform (Xo : Moduli Dw l) (c : Coeff l) :
    ModelAt Xo c ↔ ∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la → ModelAtBare Xo c la :=
  forall_congr' fun la => forall_congr' fun _ => (modelAtBare_iff Xo c la).symm

/- English proof (translation)
The claim follows from `(modelAt_iff_uniform Xo c).2 fun la hla => modelAtBare_of_modelAtSt (h la hla)`.
-/
theorem modelAt_of_modelAtSt {Xo : Moduli Dw l} {c : Coeff l}
    (h : ∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la → ModelAtSt Xo c la) : ModelAt Xo c :=
  (modelAt_iff_uniform Xo c).2 fun la hla => modelAtBare_of_modelAtSt (h la hla)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem closedSplit_iff (T : CDVR) (G : SAB H (Sp T.V)) :
    ClosedSplit T G ↔ ∃ S : SplitExt (Sp (IsLocalRing.ResidueField T.V)),
      S.IsGt ((Over.pullback (spMap (IsLocalRing.residue T.V))).obj G.G) := Iff.rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem hasUnif_iff (T : CDVR) (G : SAB H (Sp T.V)) :
    HasUnif T G ↔ ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) G, P.TorsionIso := Iff.rfl

variable (Xo : Moduli Dw l) (c : Coeff l)

def ModelAtPush : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → HasModelPush Xo c T io

def ModelOverLevelPush : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), ¬ PrimeToLevel c la →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → HasModelPush Xo c T io

/- English proof (translation)
Introduce `la hla T io e ho` and use `(h la hla T io e ho).hasModel`.
-/
theorem ModelAtPush.modelAt {Xo : Moduli Dw l} {c : Coeff l} (h : ModelAtPush Xo c) : ModelAt Xo c :=
  fun la hla T io e ho => (h la hla T io e ho).hasModel

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨fun la _ => (modelAtSt_place_iff Xo c la).1 (h la), fun la _ => (modelAtSt_place_iff Xo c la).1 (h la)⟩`. Introduce and unpack `⟨h₁, h₂⟩ la`. Distinguish the cases in `hla : PrimeToLevel c la`.

Conclude with `(modelAtSt_place_iff Xo c la).2 (h₁ la hla)`. Conclude with `(modelAtSt_place_iff Xo c la).2 (h₂ la hla)`.
-/
theorem forall_modelAtSt_iff :
    (∀ la : HeightOneSpectrum (𝓞 c.F), ModelAtSt Xo c la) ↔ ModelAtPush Xo c ∧ ModelOverLevelPush Xo c := by
  constructor
  · intro h
    exact ⟨fun la _ => (modelAtSt_place_iff Xo c la).1 (h la), fun la _ => (modelAtSt_place_iff Xo c la).1 (h la)⟩
  · rintro ⟨h₁, h₂⟩ la
    by_cases hla : PrimeToLevel c la
    · exact (modelAtSt_place_iff Xo c la).2 (h₁ la hla)
    · exact (modelAtSt_place_iff Xo c la).2 (h₂ la hla)

def UnifAtFin : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → T.FinRes →
      ∀ (y : IntFr Xo c T io) (I : IntData Xo c T io y.1), ClosedSplit T I.G → HasUnif T I.G

def UnifAtInf : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ¬ T.FinRes →
      ∀ (y : IntFr Xo c T io) (I : IntData Xo c T io y.1), ClosedSplit T I.G → HasUnif T I.G

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨fun la hla T io e ho _ => h la hla T io e ho, fun la hla T io e ho _ => h la hla T io e ho⟩`. Introduce and unpack `⟨h₁, h₂⟩ la hla T io e ho`. Distinguish the cases in `hT : T.FinRes`.

Conclude with `h₁ la hla T io e ho hT`. Conclude with `h₂ la hla T io e ho hT`.
-/
theorem unifAt_iff : UnifAt Xo c ↔ UnifAtFin Xo c ∧ UnifAtInf Xo c := by
  constructor
  · intro h
    exact ⟨fun la hla T io e ho _ => h la hla T io e ho, fun la hla T io e ho _ => h la hla T io e ho⟩
  · rintro ⟨h₁, h₂⟩ la hla T io e ho
    by_cases hT : T.FinRes
    · exact h₁ la hla T io e ho hT
    · exact h₂ la hla T io e ho hT

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h O i β Y h3 T io b hb`. Conclude with `h T io ((hasModel_iff Xo c T io).2 ⟨O, i, β, Y, b, h3, hb⟩)`. Introduce `h T io hm`. Take `⟨O, i, β, Y, b, h3, hb⟩` from `(hasModel_iff Xo c T io).1 hm`.

Conclude with `h O β Y h3 T io b hb`.
-/
theorem unifOfModel_iff : UnifOfModel Xo c ↔
    ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Y.N3 →
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V), (algebraMap T.V T.Fr).comp b = io.comp β →
        ∀ (y : IntFr Xo c T io) (I : IntData Xo c T io y.1),
          (∃ S : SplitExt (Sp (IsLocalRing.ResidueField T.V)),
            S.IsGt ((Over.pullback (spMap (IsLocalRing.residue T.V))).obj I.G.G)) →
          ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, P.TorsionIso := by
  constructor
  · intro h O i β Y h3 T io b hb
    exact h T io ((hasModel_iff Xo c T io).2 ⟨O, i, β, Y, b, h3, hb⟩)
  · intro h T io hm
    obtain ⟨O, i, β, Y, b, h3, hb⟩ := (hasModel_iff Xo c T io).1 hm
    exact h O β Y h3 T io b hb

end General

section Instance

variable {D : D7} {T : Top D}

/- English proof (translation)
The claim follows from `h.pins.2.1.2`.
-/
theorem levelA_eq_one (h : LawsP T) : T.Q.l.A = 1 := h.pins.2.1.2

/- English proof (translation)
Take `⟨hp, hq, -⟩` from `h.pins.2.2.2 j hj`. Take `⟨h1, h2⟩` from `hj`. Rewrite using `[hp, hq]`. Establish `h3` using `D.R.m_add_three_le_k`. Simplify using `only [Ranks.sigW]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem one_le_rank (h : LawsP T) {j : ℕ} (hj : InR D j) : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  obtain ⟨h1, h2⟩ := hj
  rw [hp, hq]
  have h3 := D.R.m_add_three_le_k
  simp only [Ranks.sigW]
  omega

end Instance

def ModelAtAll : Prop :=
  ∀ (D : D7) (T : Top D), LawsP T → ∀ j, InR D j → ∀ la, ModelAtSt (T.Q.Xo j) T.Q.c la

def ModelAtCore : Prop :=
  ∀ (D : D7) (T : Top D), LawsP T → ∀ j, InR D j → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F),
    ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) → ModelAtBare (T.Q.Xo j) T.Q.c la

/- English proof (translation)
Introduce `D T hT j hj la _` and use `modelAtBare_of_modelAtSt (h D T hT j hj la)`.
-/
theorem ModelAtAll.core (h : ModelAtAll) : ModelAtCore :=
  fun D T hT j hj la _ => modelAtBare_of_modelAtSt (h D T hT j hj la)

/- English proof (translation)
The claim follows from `forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_modelAtSt_iff _ _`.
-/
theorem modelAtSt_iff : ModelAtAll ↔
    ∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j →
      ModelAtPush (T.Q.Xo j) T.Q.c ∧ ModelOverLevelPush (T.Q.Xo j) T.Q.c :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_modelAtSt_iff _ _

/- English proof (translation)
Use `forall_congr' fun D => forall_congr' fun T => forall_congr' fun h => forall_congr' fun j => forall_congr' fun _ => ?_` and prove the remaining obligations. Rewrite using `[modelAt_iff_uniform]`. Conclude with `forall_congr' fun la => imp_congr_left (primeToLevel_iff _ (levelA_eq_one h) la).symm`.
-/
theorem modelAtCore_iff : ModelAtCore ↔
    ∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j → ModelAt (T.Q.Xo j) T.Q.c := by
  refine forall_congr' fun D => forall_congr' fun T => forall_congr' fun h => forall_congr' fun j =>
    forall_congr' fun _ => ?_
  rw [modelAt_iff_uniform]
  exact forall_congr' fun la => imp_congr_left (primeToLevel_iff _ (levelA_eq_one h) la).symm

/- English proof (translation)
The claim follows from `modelAtCore_iff.1 h.core`.
-/
theorem modelAt_of_modelAtAll (h : ModelAtAll) :
    ∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j → ModelAt (T.Q.Xo j) T.Q.c :=
  modelAtCore_iff.1 h.core

/- English proof (translation)
Use `forall_congr' fun D => forall_congr' fun T => forall_congr' fun h => forall_congr' fun j => forall_congr' fun _ => ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `H la hla Tc io e ho hT y I hS`. Conclude with `H Tc io y e la ho hT ((primeToLevel_iff _ (levelA_eq_one h) la).1 hla) I hS`. Introduce `H Tc io y e la ho hT hla I hS`.

Conclude with `H la ((primeToLevel_iff _ (levelA_eq_one h) la).2 hla) Tc io e ho hT y I hS`.
-/
theorem unifAtIntLaSt_iff : PullbackSections.UnifAtIntLaSt ↔
    ∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j → UnifAtFin (T.Q.Xo j) T.Q.c := by
  refine forall_congr' fun D => forall_congr' fun T => forall_congr' fun h => forall_congr' fun j =>
    forall_congr' fun _ => ?_
  constructor
  · intro H la hla Tc io e ho hT y I hS
    exact H Tc io y e la ho hT ((primeToLevel_iff _ (levelA_eq_one h) la).1 hla) I hS
  · intro H Tc io y e la ho hT hla I hS
    exact H la ((primeToLevel_iff _ (levelA_eq_one h) la).2 hla) Tc io e ho hT y I hS

/- English proof (translation)
Rewrite using `[unifAtIntLaSt_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Conclude with `⟨fun D T h j hj => ((unifAt_iff _ _).1 (H D T h j hj)).1, fun D T h j hj => ((unifAt_iff _ _).1 (H D T h j hj)).2⟩`. Introduce and unpack `⟨H₁, H₂⟩ D T h j hj`.

Conclude with `(unifAt_iff _ _).2 ⟨H₁ D T h j hj, H₂ D T h j hj⟩`.
-/
theorem unifAt_instance_iff :
    (∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j → UnifAt (T.Q.Xo j) T.Q.c) ↔
      PullbackSections.UnifAtIntLaSt ∧ ∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j → UnifAtInf (T.Q.Xo j) T.Q.c := by
  rw [unifAtIntLaSt_iff]
  constructor
  · intro H
    exact ⟨fun D T h j hj => ((unifAt_iff _ _).1 (H D T h j hj)).1,
      fun D T h j hj => ((unifAt_iff _ _).1 (H D T h j hj)).2⟩
  · rintro ⟨H₁, H₂⟩ D T h j hj
    exact (unifAt_iff _ _).2 ⟨H₁ D T h j hj, H₂ D T h j hj⟩

/- English proof (translation)
Establish `key : ∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j → ModelAt (T.Q.Xo j) T.Q.c ∧ UnifOfModel (T.Q.Xo j) T.Q.c` using `fun D T hT j hj => h _ T.Q.H (T.Q.Dw j) (one_le_rank hT hj) T.Q.l (T.Q.Xo j) T.Q.c`. Conclude with `⟨modelAtCore_iff.2 fun D T hT j hj => (key D T hT j hj).1, unifAtIntLaSt_iff.2 fun D T hT j hj => ((unifAt_iff _ _).1 (unifAt_of (key D T hT j hj).1 (key D T hT j hj).2)).1⟩`.
-/
theorem of_statement (h : Statement) : ModelAtCore ∧ PullbackSections.UnifAtIntLaSt := by
  have key : ∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j →
      ModelAt (T.Q.Xo j) T.Q.c ∧ UnifOfModel (T.Q.Xo j) T.Q.c :=
    fun D T hT j hj => h _ T.Q.H (T.Q.Dw j) (one_le_rank hT hj) T.Q.l (T.Q.Xo j) T.Q.c
  exact ⟨modelAtCore_iff.2 fun D T hT j hj => (key D T hT j hj).1,
    unifAtIntLaSt_iff.2 fun D T hT j hj =>
      ((unifAt_iff _ _).1 (unifAt_of (key D T hT j hj).1 (key D T hT j hj).2)).1⟩

/- English proof (translation)
Rewrite using `[modelAtSt_iff, unifAtIntLaSt_iff]`. Conclude with `⟨fun H D T h j hj => ⟨H.1 D T h j hj, H.2 D T h j hj⟩, fun H => ⟨fun D T h j hj => (H D T h j hj).1, fun D T h j hj => (H D T h j hj).2⟩⟩`.
-/
theorem typings_iff : (ModelAtAll ∧ PullbackSections.UnifAtIntLaSt) ↔
    ∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j →
      (ModelAtPush (T.Q.Xo j) T.Q.c ∧ ModelOverLevelPush (T.Q.Xo j) T.Q.c) ∧ UnifAtFin (T.Q.Xo j) T.Q.c := by
  rw [modelAtSt_iff, unifAtIntLaSt_iff]
  exact ⟨fun H D T h j hj => ⟨H.1 D T h j hj, H.2 D T h j hj⟩,
    fun H => ⟨fun D T h j hj => (H D T h j hj).1, fun D T h j hj => (H D T h j hj).2⟩⟩

/- English proof (translation)
Rewrite using `[modelAtCore_iff, unifAtIntLaSt_iff]`. Conclude with `⟨fun H D T h j hj => ⟨H.1 D T h j hj, H.2 D T h j hj⟩, fun H => ⟨fun D T h j hj => (H D T h j hj).1, fun D T h j hj => (H D T h j hj).2⟩⟩`.
-/
theorem typings_iff_core : (ModelAtCore ∧ PullbackSections.UnifAtIntLaSt) ↔
    ∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j →
      ModelAt (T.Q.Xo j) T.Q.c ∧ UnifAtFin (T.Q.Xo j) T.Q.c := by
  rw [modelAtCore_iff, unifAtIntLaSt_iff]
  exact ⟨fun H D T h j hj => ⟨H.1 D T h j hj, H.2 D T h j hj⟩,
    fun H => ⟨fun D T h j hj => (H D T h j hj).1, fun D T h j hj => (H D T h j hj).2⟩⟩

section Full

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

/- English proof (translation)
The claim follows from `(unifOfModel_iff Xo c).2 fun _ _ _ Y h3 T io b hb y I hS => PullbackSections.unifAtInt_of_model hE hC Y h3 T io b hb y.1 I hS`.
-/
theorem unifOfModel_of (hE : ExtVStatement) (hC : Out.CubePullSt) (Xo : Moduli Dw l) (c : Coeff l) :
    UnifOfModel Xo c :=
  (unifOfModel_iff Xo c).2 fun _ _ _ Y h3 T io b hb y I hS =>
    PullbackSections.unifAtInt_of_model hE hC Y h3 T io b hb y.1 I hS

/- English proof (translation)
The claim follows from `unifOfModel_of GlobalTheory.ModelUniqueChecks.extV_holds Out.proved_CubePullSt Xo c`.
-/
theorem unifOfModel (Xo : Moduli Dw l) (c : Coeff l) : UnifOfModel Xo c :=
  unifOfModel_of GlobalTheory.ModelUniqueChecks.extV_holds Out.proved_CubePullSt Xo c

end Full

/- English proof (translation)
Rewrite using `[typings_iff_core]`. Conclude with `⟨fun H D T h j hj => ⟨(H D T h j hj).1, unifOfModel _ _⟩, fun H D T h j hj => ⟨(H D T h j hj).1, ((unifAt_iff _ _).1 (unifAt_of (H D T h j hj).1 (H D T h j hj).2)).1⟩⟩`.
-/
theorem typings_iff_full : (ModelAtCore ∧ PullbackSections.UnifAtIntLaSt) ↔
    ∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j →
      ModelAt (T.Q.Xo j) T.Q.c ∧ UnifOfModel (T.Q.Xo j) T.Q.c := by
  rw [typings_iff_core]
  exact ⟨fun H D T h j hj => ⟨(H D T h j hj).1, unifOfModel _ _⟩,
    fun H D T h j hj => ⟨(H D T h j hj).1,
      ((unifAt_iff _ _).1 (unifAt_of (H D T h j hj).1 (H D T h j hj).2)).1⟩⟩

/- English proof (translation)
Rewrite using `[typings_iff_core]`. Conclude with `⟨fun H D T h j hj => ⟨(H D T h j hj).1, unifAt_of (H D T h j hj).1 (unifOfModel _ _)⟩, fun H D T h j hj => ⟨(H D T h j hj).1, ((unifAt_iff _ _).1 (H D T h j hj).2).1⟩⟩`.
-/
theorem typings_iff_unifAt : (ModelAtCore ∧ PullbackSections.UnifAtIntLaSt) ↔
    ∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j →
      ModelAt (T.Q.Xo j) T.Q.c ∧ UnifAt (T.Q.Xo j) T.Q.c := by
  rw [typings_iff_core]
  exact ⟨fun H D T h j hj => ⟨(H D T h j hj).1, unifAt_of (H D T h j hj).1 (unifOfModel _ _)⟩,
    fun H D T h j hj => ⟨(H D T h j hj).1, ((unifAt_iff _ _).1 (H D T h j hj).2).1⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h E _ _ _ H Dw hr l Xo c => (h E H Dw hr l Xo c).1, fun h E _ _ _ H Dw hr l Xo c => ⟨h E H Dw hr l Xo c, unifOfModel Xo c⟩⟩`.
-/
theorem statement_iff : Statement ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
      ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ModelAt Xo c :=
  ⟨fun h E _ _ _ H Dw hr l Xo c => (h E H Dw hr l Xo c).1,
    fun h E _ _ _ H Dw hr l Xo c => ⟨h E H Dw hr l Xo c, unifOfModel Xo c⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ _ _ _ _ _ Xo c la => modelAtSt_place_iff Xo c la, fun _ _ _ _ _ _ _ Xo c => modelAt_iff_uniform Xo c, fun _ _ _ _ _ _ _ _ _ => modelAt_of_modelAtSt, unifAtIntLaSt_iff, typings_iff, typings_iff_full, typings_iff_unifAt, fun h => ⟨h.1.core, h.2⟩, of_statement, statement_if …`.
-/
theorem typings_compared :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)), ModelAtSt Xo c la ↔
        ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
          ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (b : O →+* T.V) (Y : Model Xo c β),
            (∀ x : O, algebraMap T.V T.Fr (b x) = io (β x)) ∧ Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L) ∧
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), ModelAt Xo c ↔ ∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la →
        ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (Y : Model Xo c β), Y.N3 ∧
          ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
            ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = io.comp β) ∧
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l),
        (∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la → ModelAtSt Xo c la) → ModelAt Xo c) ∧
    (PullbackSections.UnifAtIntLaSt ↔ ∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j →
      ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), PrimeToLevel T.Q.c la →
        ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (e : ℕ), OverLa la Tc.V io e → Tc.FinRes →
          ∀ (y : IntFr (T.Q.Xo j) T.Q.c Tc io) (I : IntData (T.Q.Xo j) T.Q.c Tc io y.1),
            ClosedSplit Tc I.G → HasUnif Tc I.G) ∧
    ((ModelAtAll ∧ PullbackSections.UnifAtIntLaSt) ↔ ∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j →
      (ModelAtPush (T.Q.Xo j) T.Q.c ∧ ModelOverLevelPush (T.Q.Xo j) T.Q.c) ∧ UnifAtFin (T.Q.Xo j) T.Q.c) ∧
    ((ModelAtCore ∧ PullbackSections.UnifAtIntLaSt) ↔ ∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j →
      ModelAt (T.Q.Xo j) T.Q.c ∧ UnifOfModel (T.Q.Xo j) T.Q.c) ∧
    ((ModelAtCore ∧ PullbackSections.UnifAtIntLaSt) ↔ ∀ (D : D7) (T : Top D), LawsP T → ∀ j : ℕ, InR D j →
      ModelAt (T.Q.Xo j) T.Q.c ∧ UnifAt (T.Q.Xo j) T.Q.c) ∧
    (ModelAtAll ∧ PullbackSections.UnifAtIntLaSt → ModelAtCore ∧ PullbackSections.UnifAtIntLaSt) ∧
    (Statement → ModelAtCore ∧ PullbackSections.UnifAtIntLaSt) ∧
    (Statement ↔ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H),
      1 ≤ Dw.p + Dw.q → ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ModelAt Xo c) :=
  ⟨fun _ _ _ _ _ _ _ Xo c la => modelAtSt_place_iff Xo c la, fun _ _ _ _ _ _ _ Xo c => modelAt_iff_uniform Xo c,
    fun _ _ _ _ _ _ _ _ _ => modelAt_of_modelAtSt, unifAtIntLaSt_iff, typings_iff, typings_iff_full,
    typings_iff_unifAt, fun h => ⟨h.1.core, h.2⟩, of_statement, statement_iff⟩

end GlobalTheory.Proof.ModelAtPrimeToLevel
