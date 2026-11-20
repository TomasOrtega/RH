import Mathlib

namespace GlobalTheory

/- English proof (translation)
Set `K` to `FractionRing R`. Set `K₀ : Subfield K` to `Subfield.closure (algebraMap R K '' S)`. Set `R₀ : Subring R` to `K₀.toSubring.comap (algebraMap R K)`. Establish `hinj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Establish `hmem : ∀ x : R, x ∈ R₀ ↔ algebraMap R K x ∈ K₀` using `fun x => Iff.rfl`.

Establish `hdvd : ∀ a b : R₀, (a : R) ∣ (b : R) → a ∣ b`. Introduce and unpack `a b ⟨c, hc⟩`. Distinguish the cases in `ha : (a : R) = 0`. Establish `: b = 0` using `Subtype.ext (by rw [hc, ha]; simp)`. Rewrite using `[this]`.

Conclude with `dvd_zero _`. Establish `ha' : algebraMap R K a ≠ 0` using `fun h => ha (hinj (by simpa using h))`. Establish `hcm : c ∈ R₀`. Rewrite using `[hmem]`. Establish `: algebraMap R K c = algebraMap R K b / algebraMap R K a`.

Rewrite using `[hc, map_mul, mul_div_cancel_left₀ _ ha']`. Rewrite using `[this]`. Conclude with `K₀.div_mem ((hmem _).1 b.2) ((hmem _).1 a.2)`. Conclude with `⟨⟨c, hcm⟩, Subtype.ext hc⟩`. Establish `hloc : IsLocalHom R₀.subtype` using `⟨fun a ha => by`.

Rewrite `ha`, the goal using `[isUnit_iff_dvd_one]`. Conclude with `hdvd a 1 ha⟩`. Establish `hlr : IsLocalRing R₀` using `RingHom.domain_isLocalRing R₀.subtype`. Establish `hpid : IsPrincipalIdealRing R₀` using `⟨fun I => by`. Take `⟨M, ⟨a, haI, rfl⟩, hM⟩` from `set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) {J : Ideal R | ∃ a : R₀, a ∈ I ∧ Ideal.span {(a : R)} = J} ⟨_, 0, I.zero_mem, rfl⟩`.

Use `⟨⟨a, le_antisymm (fun b hb => ?_) ?_⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `b ∈ Ideal.span {a}`. Rewrite using `[Ideal.mem_span_singleton]`. Apply `hdvd` to reduce the goal to its premises. Break down `ValuationRing.dvd_total (a : R) (b : R) with h | h` into its components or cases.

Conclude with `h`. Establish `h1 : Ideal.span {(a : R)} ≤ Ideal.span {(b : R)}` using `Ideal.span_singleton_le_span_singleton.mpr h`. Establish `h2` using `hM _ ⟨b, hb, rfl⟩`. Conclude with `Ideal.span_singleton_le_span_singleton.mp (eq_of_le_of_not_lt h1 h2).ge`. Conclude with `(Ideal.span_singleton_le_iff_mem I).mpr haI⟩`.

Establish `hK : Countable K₀`. Rewrite using `[← Cardinal.mk_le_aleph0_iff]`. Use `(Subfield.cardinalMk_closure_le_max _).trans (max_le ?_ le_rfl)` and prove the remaining obligations. Rewrite using `[Cardinal.mk_le_aleph0_iff]`. Conclude with `(hS.image _).to_subtype`.

Establish `hc : Countable R₀`. Set `f : R₀ → K₀` to `fun x => ⟨algebraMap R K x, (hmem _).1 x.2⟩`. Establish `: Function.Injective f` using `fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))`. Conclude with `this.countable`. Use `⟨R₀, hlr, hpid, hc, fun x hx => Subfield.subset_closure ⟨x, hx, rfl⟩, hloc, ?_⟩` and prove the remaining obligations.

Establish `: IsLocalHom (algebraMap R₀ R)` using `hloc`. Establish `: Module.Flat R₀ R` using `inferInstance`. Conclude with `Module.FaithfullyFlat.of_flat_of_isLocalHom`.
-/
theorem exists_countable_local_pid_subring (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsPrincipalIdealRing R] (S : Set R) (hS : S.Countable) :
    ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀),
      Countable R₀ ∧ S ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ Module.FaithfullyFlat R₀ R := by
  classical
  let K := FractionRing R
  let K₀ : Subfield K := Subfield.closure (algebraMap R K '' S)
  let R₀ : Subring R := K₀.toSubring.comap (algebraMap R K)
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmem : ∀ x : R, x ∈ R₀ ↔ algebraMap R K x ∈ K₀ := fun x => Iff.rfl
  have hdvd : ∀ a b : R₀, (a : R) ∣ (b : R) → a ∣ b := by
    rintro a b ⟨c, hc⟩
    by_cases ha : (a : R) = 0
    · have : b = 0 := Subtype.ext (by rw [hc, ha]; simp)
      rw [this]; exact dvd_zero _
    · have ha' : algebraMap R K a ≠ 0 := fun h => ha (hinj (by simpa using h))
      have hcm : c ∈ R₀ := by
        rw [hmem]
        have : algebraMap R K c = algebraMap R K b / algebraMap R K a := by
          rw [hc, map_mul, mul_div_cancel_left₀ _ ha']
        rw [this]
        exact K₀.div_mem ((hmem _).1 b.2) ((hmem _).1 a.2)
      exact ⟨⟨c, hcm⟩, Subtype.ext hc⟩
  have hloc : IsLocalHom R₀.subtype := ⟨fun a ha => by
    rw [isUnit_iff_dvd_one] at ha ⊢
    exact hdvd a 1 ha⟩
  have hlr : IsLocalRing R₀ := RingHom.domain_isLocalRing R₀.subtype
  have hpid : IsPrincipalIdealRing R₀ := ⟨fun I => by
    obtain ⟨M, ⟨a, haI, rfl⟩, hM⟩ := set_has_maximal_iff_noetherian.mpr
      (inferInstance : IsNoetherian R R)
      {J : Ideal R | ∃ a : R₀, a ∈ I ∧ Ideal.span {(a : R)} = J} ⟨_, 0, I.zero_mem, rfl⟩
    refine ⟨⟨a, le_antisymm (fun b hb => ?_) ?_⟩⟩
    · change b ∈ Ideal.span {a}
      rw [Ideal.mem_span_singleton]
      apply hdvd
      rcases ValuationRing.dvd_total (a : R) (b : R) with h | h
      · exact h
      · have h1 : Ideal.span {(a : R)} ≤ Ideal.span {(b : R)} :=
          Ideal.span_singleton_le_span_singleton.mpr h
        have h2 := hM _ ⟨b, hb, rfl⟩
        exact Ideal.span_singleton_le_span_singleton.mp (eq_of_le_of_not_lt h1 h2).ge
    · exact (Ideal.span_singleton_le_iff_mem I).mpr haI⟩
  have hK : Countable K₀ := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (Subfield.cardinalMk_closure_le_max _).trans (max_le ?_ le_rfl)
    rw [Cardinal.mk_le_aleph0_iff]
    exact (hS.image _).to_subtype
  have hc : Countable R₀ := by
    let f : R₀ → K₀ := fun x => ⟨algebraMap R K x, (hmem _).1 x.2⟩
    have : Function.Injective f := fun x y h =>
      Subtype.ext (hinj (congrArg Subtype.val h))
    exact this.countable
  refine ⟨R₀, hlr, hpid, hc, fun x hx => Subfield.subset_closure ⟨x, hx, rfl⟩, hloc, ?_⟩
  have : IsLocalHom (algebraMap R₀ R) := hloc
  have : Module.Flat R₀ R := inferInstance
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end GlobalTheory
