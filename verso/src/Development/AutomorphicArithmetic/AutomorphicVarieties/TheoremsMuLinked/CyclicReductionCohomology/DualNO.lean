import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.NcardTraceZeroTwistedCocyclesLeCoboundariesMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DescendO
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.TwistedCocycleApplyOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.LcOfOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PolZCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.FinTwO
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.CCount

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

/- English proof (translation)
Take `⟨c1, c2, c3⟩` from `cCount R Γ M ρ c hc h2`. Establish `c1` using `c1 Z hf hB hZ`. Use `haveI : Nonempty {m : M // ρ c m = m} := ⟨⟨0, map_zero _⟩⟩`. Establish `hp : 0 < Nat.card {m : M // ρ c m = m}` using `Nat.card_pos`. Use `Nat.le_of_mul_le_mul_right ?_ hp` and prove the remaining obligations.

Rewrite using `[c1, ← c2, ← c3]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem cnt {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M] [Finite M]
    (ρ : Representation R Γ M) (c : Γ) (hc : c * c = 1) (h2 : IsUnit (2 : R)) (Z : AddSubgroup (Γ → M)) (hf : Finite Z)
    (hB : (Bl ρ).toAddSubgroup ≤ Z) (hZ : ∀ z ∈ Z, ∀ g h, z (g * h) = z g + ρ g (z h)) (K : ℕ)
    (h : {z | z ∈ Z ∧ z c = 0}.ncard ≤ {z | z ∈ Bl ρ ∧ z c = 0}.ncard * K) : Nat.card Z ≤ Nat.card (Bl ρ) * K := by
  obtain ⟨c1, c2, c3⟩ := cCount R Γ M ρ c hc h2
  have c1 := c1 Z hf hB hZ
  haveI : Nonempty {m : M // ρ c m = m} := ⟨⟨0, map_zero _⟩⟩
  have hp : 0 < Nat.card {m : M // ρ c m = m} := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hp
  rw [c1, ← c2, ← c3]
  calc _ ≤ ({z | z ∈ Bl ρ ∧ z c = 0}.ncard * K) * (Nat.card (Bl ρ) * Nat.card ρ.invariants) := Nat.mul_le_mul_right _ h
    _ = _ := by ring

/- English proof (translation)
Introduce `g0`. Take `⟨g, hg⟩` from `h.surj g0`. Use `⟨⟨g, ?_⟩, Subtype.ext hg⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.mem_ker, ← h.η, hg]`. Conclude with `g0.2`.
-/
private theorem sec {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) : Function.Surjective h.p₀ := by
  intro g0
  obtain ⟨g, hg⟩ := h.surj g0
  refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
  rw [MonoidHom.mem_ker, ← h.η, hg]
  exact g0.2

/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

/- English proof (translation)
The claim follows from `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) :
    red m (1 : Matrix (Fin n) (Fin n) O) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨red m P, red m (P⁻¹ : GL (Fin n) O), by rw [← red_mul, P.mul_inv, red_one], by rw [← red_mul, P.inv_mul, red_one]⟩, rfl⟩`.
-/
private theorem red_unit {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (P : GL (Fin n) O) :
    IsUnit (red m (P : Matrix (Fin n) (Fin n) O)) :=
  ⟨⟨red m P, red m (P⁻¹ : GL (Fin n) O), by rw [← red_mul, P.mul_inv, red_one], by rw [← red_mul, P.inv_mul, red_one]⟩, rfl⟩

/- English proof (translation)
Establish `hc : B * A ^ k * A = A ^ k`. Rewrite using `[Matrix.mul_assoc, ← pow_succ, pow_succ', ← Matrix.mul_assoc, h, Matrix.one_mul]`. Rewrite using `[Matrix.sub_mul, Matrix.trace_sub, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm A, Matrix.mul_assoc, hc, sub_self]`.
-/
private theorem tr_comm {R : Type} [CommRing R] {n : ℕ} (A B Y : Matrix (Fin n) (Fin n) R) (h : B * A = 1) (k : ℕ) :
    ((A * Y * B - Y) * A ^ k).trace = 0 := by
  have hc : B * A ^ k * A = A ^ k := by
    rw [Matrix.mul_assoc, ← pow_succ, pow_succ', ← Matrix.mul_assoc, h, Matrix.one_mul]
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm A, Matrix.mul_assoc, hc,
    sub_self]

/- English proof (translation)
Introduce `l _ L G0 T O _ _ _ _ _ n x hl hc hΦ hPL hdet`. Take `⟨C, hC⟩` from `ncard_traceZero_twisted_cocycles_le_coboundaries_mul l L G0 O n x T.q T.sg hΦ hdet`. Use `⟨C, fun m => ?_⟩` and prove the remaining obligations. Use `filter_upwards [phEqO l L G0 T O n x m hΦ hPL] with N hN rep hAd hfin`. Take `⟨h2, hO⟩` from `omFacts l O`.

Use `haveI : Finite (Om O m) := (hO m).1`. Use `haveI : Finite (Mm O n m) := inferInstanceAs (Finite (Fin n → Fin n → Om O m))`. Establish `hLC : LC rep` using `(adExP l L (T.GN N) G0 (T.h N) O n x m).2.2 rep (Or.inr hAd)`. Establish `r1 : x.ρ0 m 1 = 1` using `by show red m ((x.ρ 1 : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1`. Rewrite using `[map_one, Units.val_one, red_one]`.

Establish `rmul : ∀ g g', x.ρ0 m (g * g') = x.ρ0 m g * x.ρ0 m g'` using `fun g g' => by show red m ((x.ρ (g * g') : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = _`. Rewrite using `[map_mul, Units.val_mul, red_mul]`. Both sides reduce to the same expression. Establish `hε : ∀ g, epsm O (T.GN N) m g = epsm O G0 m ((T.h N).p g)` using `fun g => by`. Unfold `epsm`.

Rewrite using `[(T.h N).ε]`. Establish `hA : ∀ (g : (T.GN N).G₀) Y, rep g Y = epsm O G0 m ((T.h N).p g) • (x.ρ0 m ((T.h N).p₀ g) * Y * x.ρ0 m ((T.h N).p₀ g)⁻¹)` using `fun g Y => by`. Rewrite using `[hAd.1, hε, ← map_inv]`. Both sides reduce to the same expression. Establish `hP` using `red_unit m x.P`.

Take `⟨s, hs⟩` from `(sec (T.h N)).hasRightInverse`. Set `Z : AddSubgroup ((T.GN N).Γ → Mm O n m)` to `{ carrier := {y | y ∈ Zl rep ∧ ∀ j, ∃ Y, y (T.ph N j) = rep (T.ph N j) Y - Y ∧ y (T.ta N j) = rep (T.ta N j) Y - Y} add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun j => by`. Take `⟨Y, e1, e2⟩` from `ha.2 j`. Take `⟨Y', e3, e4⟩` from `hb.2 j`. Conclude with `⟨Y + Y', by rw [Pi.add_apply, e1, e3, map_add]; abel, by rw [Pi.add_apply, e2, e4, map_add]; abel⟩⟩`.

Use the proof step `zero_mem' := ⟨zero_mem _, fun j => ⟨0, by simp, by simp⟩⟩`. Use the proof step `neg_mem' := fun {a} ha => ⟨neg_mem ha.1, fun j => by`. Take `⟨Y, e1, e2⟩` from `ha.2 j`. Conclude with `⟨-Y, by rw [Pi.neg_apply, e1, map_neg]; abel, by rw [Pi.neg_apply, e2, map_neg]; abel⟩⟩ }`. Establish `hBZl : ∀ y ∈ Bl rep, y ∈ Zl rep`.

Introduce `y hy`. Take `⟨Y, hY⟩` from `(mem_Bl rep).1 hy`. Establish `: y = fun g => rep g Y - Y` using `funext hY`. Substitute `this` using the available equality. Conclude with `⟨(hLC Y).comp (· - Y), fun g h => by simp only [map_mul, Module.End.mul_apply, map_sub]; abel⟩`.

Establish `hZlf : {y | y ∈ Zl rep}.Finite` using `hfin`. Establish `hZf : Finite Z` using `(hZlf.subset fun y hy => hy.1 : {y | y ∈ Z}.Finite)`. Set `f : ((T.GN N).Γ → Mm O n m) → (G0.G₀ → Mm O n m)` to `fun y g => y (s g)`. Establish `hta : ∀ j Y, rep (T.ta N j) Y = Y`. Introduce `j Y`.

Establish `e : (T.h N).p₀ (T.ta N j) = 1` using `Subtype.ext (T.ta_ker N j)`. Rewrite using `[hA]`. Simplify using `only [e, inv_one, r1, T.ta_ker N j, epsm, map_one, Units.val_one, one_smul, mul_one, one_mul]`. Establish `hdesc : ∀ y, y ∈ Z ∧ y (T.GN N).c = 0 → f y ∈ Tw x m ∧ ∀ g : (T.GN N).G₀, y g = f y ((T.h N).p₀ g)`. Introduce `y hy`.

Take `⟨z, hz, e⟩` from `descendO l L G0 T O n x m N rep hc hPL hAd y hy.1.1 hy.2 fun j => by`. Take `⟨Y, -, e2⟩` from `hy.1.2 j`. Rewrite using `[e2, hta, sub_self]`. Establish `: f y = z` using `funext fun g => by show y (s g) = z g`. Rewrite using `[e, hs g]`.

Rewrite using `[this]`. Conclude with `⟨hz, e⟩`. Establish `s1 : {y | y ∈ Z ∧ y (T.GN N).c = 0}.ncard ≤ {z | z ∈ Tw x m ∧ ∀ j (k : ℕ), (z (T.sg j) * x.ρ0 m (T.sg j) ^ k).trace = 0}.ncard`. Use `Set.ncard_le_ncard_of_injOn f (fun y hy => ⟨(hdesc y hy).1, fun j k => ?_⟩) (fun y hy y' hy' e => ?_) ((finTwO l L G0 O n x m hΦ).subset fun z hz => hz.1)` and prove the remaining obligations. Take `⟨a1, a2, a3⟩` from `hN j`.

Take `⟨Y, e1, -⟩` from `hy.1.2 j`. Establish `hi : x.ρ0 m ((T.h N).p₀ (T.ph N j))⁻¹ * x.ρ0 m (T.sg j) = 1`. Rewrite using `[← a1, ← rmul, inv_mul_cancel, r1]`. Rewrite using `[← a3 _ (hdesc y hy).1, ← (hdesc y hy).2, e1, hA, a2, a1, one_smul]`. Conclude with `tr_comm _ _ _ hi k`.

Establish `h0` using `((polP l (T.GN N).frame O _ n _ _ _ rep hP hAd).2 (y - y') (sub_mem hy.1.1 hy'.1.1) (by show y (T.GN N).c - y' (T.GN N).c = 0; rw [hy.2, hy'.2, sub_self])).2 fun g => by show y g - y' g = 0`. Rewrite using `[sub_eq_zero, (hdesc y hy).2, (hdesc y' hy').2, e]`. Conclude with `sub_eq_zero.1 h0`. Establish `s2 : (TwB x m).ncard ≤ {z | z ∈ Bl rep ∧ z (T.GN N).c = 0}.ncard`. Establish `hf : {z | z ∈ Bl rep ∧ z (T.GN N).c = 0}.Finite` using `hZlf.subset fun y hy => hBZl y hy.1`.

Use `le_trans (Set.ncard_le_ncard (fun z hz => ?_) (hf.image f)) (Set.ncard_image_le hf)` and prove the remaining obligations. Take `⟨Y, e1, rfl⟩` from `hz`. Use `⟨fun g => rep g Y - Y, ⟨(mem_Bl rep).2 ⟨_, fun _ => rfl⟩, ?_⟩, funext fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[sub_eq_zero]`. Apply `hP.mul_left_cancel` to reduce the goal to its premises.

Use `(hAd.2 _).trans ?_` and prove the remaining obligations. Use `show -(epsm O (T.GN N) m (T.GN N).c • (Yᵀ * _)) = _`. Rewrite using `[hε, (T.h N).c, e1]`. Simplify using `only [epsm, hc, Units.val_neg, Units.val_one, map_neg, map_one, neg_smul, one_smul, neg_neg]`. Use `show rep (s g) Y - Y = _`.

Establish `e : (T.h N).p (s g) = g` using `congrArg Subtype.val (hs g)`. Rewrite using `[hA, hs g, e]`. Use `cnt rep (T.GN N).c (T.GN N).frame.c_sq (h2 hl) Z hZf (fun y hy => ⟨hBZl y hy, fun j => by` as an intermediate fact. Take `⟨Y, hY⟩` from `(mem_Bl rep).1 hy`. Conclude with `⟨Y, hY _, hY _⟩⟩) (fun z hz => hz.1.2) _ (s1.trans ((hC m).trans (Nat.mul_le_mul_right _ s2)))`.

Rewrite using `[← Nat.card_coe_set_eq]` and apply the resulting hypothesis.
-/
theorem UpperTheory.V.Th.dualNO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n), l ≠ 2 → G0.ε G0.c = -1 → PhiCond G0.Γ l → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → DetO y (Set.range T.sg) → ∃ C : ℕ, ∀ m, ∀ᶠ N in atTop, ∀ rep' : Representation O (T.GN N).Γ (Mm O n m), IsAd1 (T.h N) y m rep' → Finite (Zl rep') → {z | z ∈ Zl rep' ∧ ∀ j, ∃ Y, z (T.ph N j) = rep' (T.ph N j) Y - Y ∧ z (T.ta N j) = rep' (T.ta N j) Y - Y}.ncard ≤ Nat.card (Bl rep') * Nat.card (ResidueField O) ^ C := by
  intro l _ L G0 T O _ _ _ _ _ n x hl hc hΦ hPL hdet
  obtain ⟨C, hC⟩ := ncard_traceZero_twisted_cocycles_le_coboundaries_mul l L G0 O n x T.q T.sg hΦ hdet
  refine ⟨C, fun m => ?_⟩
  filter_upwards [phEqO l L G0 T O n x m hΦ hPL] with N hN rep hAd hfin
  obtain ⟨h2, hO⟩ := omFacts l O
  haveI : Finite (Om O m) := (hO m).1
  haveI : Finite (Mm O n m) := inferInstanceAs (Finite (Fin n → Fin n → Om O m))
  have hLC : LC rep := (adExP l L (T.GN N) G0 (T.h N) O n x m).2.2 rep (Or.inr hAd)
  have r1 : x.ρ0 m 1 = 1 := by
    show red m ((x.ρ 1 : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1
    rw [map_one, Units.val_one, red_one]
  have rmul : ∀ g g', x.ρ0 m (g * g') = x.ρ0 m g * x.ρ0 m g' := fun g g' => by
    show red m ((x.ρ (g * g') : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = _
    rw [map_mul, Units.val_mul, red_mul]
    rfl
  have hε : ∀ g, epsm O (T.GN N) m g = epsm O G0 m ((T.h N).p g) := fun g => by
    unfold epsm
    rw [(T.h N).ε]
  have hA : ∀ (g : (T.GN N).G₀) Y, rep g Y = epsm O G0 m ((T.h N).p g) •
      (x.ρ0 m ((T.h N).p₀ g) * Y * x.ρ0 m ((T.h N).p₀ g)⁻¹) := fun g Y => by
    rw [hAd.1, hε, ← map_inv]
    rfl
  have hP := red_unit m x.P
  obtain ⟨s, hs⟩ := (sec (T.h N)).hasRightInverse
  let Z : AddSubgroup ((T.GN N).Γ → Mm O n m) :=
    { carrier := {y | y ∈ Zl rep ∧ ∀ j, ∃ Y, y (T.ph N j) = rep (T.ph N j) Y - Y ∧ y (T.ta N j) = rep (T.ta N j) Y - Y}
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun j => by
        obtain ⟨Y, e1, e2⟩ := ha.2 j
        obtain ⟨Y', e3, e4⟩ := hb.2 j
        exact ⟨Y + Y', by rw [Pi.add_apply, e1, e3, map_add]; abel, by rw [Pi.add_apply, e2, e4, map_add]; abel⟩⟩
      zero_mem' := ⟨zero_mem _, fun j => ⟨0, by simp, by simp⟩⟩
      neg_mem' := fun {a} ha => ⟨neg_mem ha.1, fun j => by
        obtain ⟨Y, e1, e2⟩ := ha.2 j
        exact ⟨-Y, by rw [Pi.neg_apply, e1, map_neg]; abel, by rw [Pi.neg_apply, e2, map_neg]; abel⟩⟩ }
  have hBZl : ∀ y ∈ Bl rep, y ∈ Zl rep := by
    intro y hy
    obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hy
    have : y = fun g => rep g Y - Y := funext hY
    subst this
    exact ⟨(hLC Y).comp (· - Y), fun g h => by simp only [map_mul, Module.End.mul_apply, map_sub]; abel⟩
  have hZlf : {y | y ∈ Zl rep}.Finite := hfin
  have hZf : Finite Z := (hZlf.subset fun y hy => hy.1 : {y | y ∈ Z}.Finite)
  let f : ((T.GN N).Γ → Mm O n m) → (G0.G₀ → Mm O n m) := fun y g => y (s g)
  have hta : ∀ j Y, rep (T.ta N j) Y = Y := by
    intro j Y
    have e : (T.h N).p₀ (T.ta N j) = 1 := Subtype.ext (T.ta_ker N j)
    rw [hA]
    simp only [e, inv_one, r1, T.ta_ker N j, epsm, map_one, Units.val_one, one_smul, mul_one, one_mul]
  have hdesc : ∀ y, y ∈ Z ∧ y (T.GN N).c = 0 → f y ∈ Tw x m ∧
      ∀ g : (T.GN N).G₀, y g = f y ((T.h N).p₀ g) := by
    intro y hy
    obtain ⟨z, hz, e⟩ := descendO l L G0 T O n x m N rep hc hPL hAd y hy.1.1 hy.2 fun j => by
      obtain ⟨Y, -, e2⟩ := hy.1.2 j
      rw [e2, hta, sub_self]
    have : f y = z := funext fun g => by
      show y (s g) = z g
      rw [e, hs g]
    rw [this]
    exact ⟨hz, e⟩
  have s1 : {y | y ∈ Z ∧ y (T.GN N).c = 0}.ncard ≤
      {z | z ∈ Tw x m ∧ ∀ j (k : ℕ), (z (T.sg j) * x.ρ0 m (T.sg j) ^ k).trace = 0}.ncard := by
    refine Set.ncard_le_ncard_of_injOn f (fun y hy => ⟨(hdesc y hy).1, fun j k => ?_⟩) (fun y hy y' hy' e => ?_)
      ((finTwO l L G0 O n x m hΦ).subset fun z hz => hz.1)
    · obtain ⟨a1, a2, a3⟩ := hN j
      obtain ⟨Y, e1, -⟩ := hy.1.2 j
      have hi : x.ρ0 m ((T.h N).p₀ (T.ph N j))⁻¹ * x.ρ0 m (T.sg j) = 1 := by
        rw [← a1, ← rmul, inv_mul_cancel, r1]
      rw [← a3 _ (hdesc y hy).1, ← (hdesc y hy).2, e1, hA, a2, a1, one_smul]
      exact tr_comm _ _ _ hi k
    · have h0 := ((polP l (T.GN N).frame O _ n _ _ _ rep hP hAd).2 (y - y') (sub_mem hy.1.1 hy'.1.1)
        (by show y (T.GN N).c - y' (T.GN N).c = 0; rw [hy.2, hy'.2, sub_self])).2 fun g => by
          show y g - y' g = 0
          rw [sub_eq_zero, (hdesc y hy).2, (hdesc y' hy').2, e]
      exact sub_eq_zero.1 h0
  have s2 : (TwB x m).ncard ≤ {z | z ∈ Bl rep ∧ z (T.GN N).c = 0}.ncard := by
    have hf : {z | z ∈ Bl rep ∧ z (T.GN N).c = 0}.Finite := hZlf.subset fun y hy => hBZl y hy.1
    refine le_trans (Set.ncard_le_ncard (fun z hz => ?_) (hf.image f)) (Set.ncard_image_le hf)
    obtain ⟨Y, e1, rfl⟩ := hz
    refine ⟨fun g => rep g Y - Y, ⟨(mem_Bl rep).2 ⟨_, fun _ => rfl⟩, ?_⟩, funext fun g => ?_⟩
    · rw [sub_eq_zero]
      apply hP.mul_left_cancel
      refine (hAd.2 _).trans ?_
      show -(epsm O (T.GN N) m (T.GN N).c • (Yᵀ * _)) = _
      rw [hε, (T.h N).c, e1]
      simp only [epsm, hc, Units.val_neg, Units.val_one, map_neg, map_one, neg_smul, one_smul, neg_neg]
    · show rep (s g) Y - Y = _
      have e : (T.h N).p (s g) = g := congrArg Subtype.val (hs g)
      rw [hA, hs g, e]
  have := cnt rep (T.GN N).c (T.GN N).frame.c_sq (h2 hl) Z hZf
    (fun y hy => ⟨hBZl y hy, fun j => by
      obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hy
      exact ⟨Y, hY _, hY _⟩⟩) (fun z hz => hz.1.2) _ (s1.trans ((hC m).trans (Nat.mul_le_mul_right _ s2)))
  rwa [← Nat.card_coe_set_eq]
