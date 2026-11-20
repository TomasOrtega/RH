import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoreStepOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.RetractionReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.SesquilinearRepresentation
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.DualFamilyExists

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.SRW

/- English proof (translation)
The claim follows from `(I : Submodule (𝓞 E) E).zero_mem`.
-/
theorem fi_zero {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    (0 : E) ∈ I := (I : Submodule (𝓞 E) E).zero_mem

/- English proof (translation)
The claim follows from `(I : Submodule (𝓞 E) E).add_mem hx hy`.
-/
theorem fi_add {E : Type} [Field E] [NumberField E] {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}
    {x y : E} (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := (I : Submodule (𝓞 E) E).add_mem hx hy

/- English proof (translation)
The claim follows from `(I : Submodule (𝓞 E) E).smul_mem o hx`.
-/
theorem fi_smul {E : Type} [Field E] [NumberField E] {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}
    (o : 𝓞 E) {x : E} (hx : x ∈ I) : o • x ∈ I := (I : Submodule (𝓞 E) E).smul_mem o hx

/- English proof (translation)
The claim follows from `(IsScalarTower.algebraMap_smul E o v).symm`.
-/
theorem osmul {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (o : 𝓞 E) (v : V) : o • v = (o : E) • v := (IsScalarTower.algebraMap_smul E o v).symm

/- English proof (translation)
Use `⟨algebraMap ℚ E (1 / 2), fun o ho => ?_⟩` and prove the remaining obligations. Establish `hint : IsIntegral ℤ (algebraMap ℚ E (1 / 2))`. Rewrite using `[← ho]`. Conclude with `o.2`. Establish `hq : IsIntegral ℤ ((1 : ℚ) / 2)` using `(isIntegral_algHom_iff (x := (1 : ℚ) / 2) (IsScalarTower.toAlgHom ℤ ℚ E) (algebraMap ℚ E).injective).mp hint`.

Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hq`. Establish `hn' : (n : ℚ) = 1 / 2`. Rewrite using `[← hn]`. Simplify using the standard rewrite rules. Establish `h2 : ((2 * n : ℤ) : ℚ) = 1`.

Use `push_cast`. Rewrite using `[hn']`. Evaluate the numerical expressions. Establish `h3 : (2 * n : ℤ) = 1` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_not_int {E : Type} [Field E] [NumberField E] : ∃ c : E, ∀ o : 𝓞 E, (o : E) ≠ c := by
  refine ⟨algebraMap ℚ E (1 / 2), fun o ho => ?_⟩
  have hint : IsIntegral ℤ (algebraMap ℚ E (1 / 2)) := by
    rw [← ho]
    exact o.2
  have hq : IsIntegral ℤ ((1 : ℚ) / 2) :=
    (isIntegral_algHom_iff (x := (1 : ℚ) / 2) (IsScalarTower.toAlgHom ℤ ℚ E) (algebraMap ℚ E).injective).mp hint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  have hn' : (n : ℚ) = 1 / 2 := by
    rw [← hn]
    simp
  have h2 : ((2 * n : ℤ) : ℚ) = 1 := by
    push_cast
    rw [hn']
    norm_num
  have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

/- English proof (translation)
Simplify using `[orth]`.
-/
theorem mem_orth_iff {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}
    {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth]

/- English proof (translation)
Introduce `y hy`. Establish `hy' : y ∈ Submodule.span E (Set.range F0.e)` using `hy`. Use `clear hy`. Proceed by induction on `hy' using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨a, rfl⟩` from `hx`. Conclude with `hv a`. Consider the case `zero => simp`. Consider the case `add x w _ _ hx hw => simp [hx, hw]`. Consider the case `smul c x _ hx => simp [hx]`.
-/
theorem hX_left {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F0 : FlagG S r T) {v : S.V} (hv : ∀ a, S.hT (F0.e a) v = 0) : ∀ y ∈ F0.X, S.hT y v = 0 := by
  intro y hy
  have hy' : y ∈ Submodule.span E (Set.range F0.e) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact hv a
  | zero => simp
  | add x w _ _ hx hw => simp [hx, hw]
  | smul c x _ hx => simp [hx]

/- English proof (translation)
Introduce `x hx`. Rewrite using `[mem_orth_iff]`. Apply `hX_left F0` to reduce the goal to its premises. Introduce `a`. Establish `hx' : x ∈ Submodule.span E (Set.range F0.e)` using `hx`.

Use `clear hx`. Proceed by induction on `hx' using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨b, rfl⟩` from `hy`. Conclude with `F0.e_iso a b`.

Consider the case `zero => simp`. Consider the case `add y w _ _ hy hw => simp [hy, hw]`. Consider the case `smul c y _ hy => simp [hy]`.
-/
theorem X_le_orth {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F0 : FlagG S r T) : F0.X ≤ orth S F0.X := by
  intro x hx
  rw [mem_orth_iff]
  apply hX_left F0
  intro a
  have hx' : x ∈ Submodule.span E (Set.range F0.e) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact F0.e_iso a b
  | zero => simp
  | add y w _ _ hy hw => simp [hy, hw]
  | smul c y _ hy => simp [hy]

/- English proof (translation)
Introduce `E _ _ _ S r T aa F0 Λ hC`. Take `⟨hlat, huni, hz, hprim, hX, haa, hcs, htr⟩` from `hC`. Establish `hXL : Λ ⊓ (F0.X).restrictScalars (𝓞 E) = Formalism.L2.SG.Saturated.latSpan aa F0.e` using `hX`. Establish `hzo : ∀ y ∈ F0.X, S.hT y F0.z = 0` using `hX_left F0 F0.z_orth`. Establish `hXo : F0.X ≤ orth S F0.X` using `X_le_orth F0`.

Establish `hzorth : F0.z ∈ orth S F0.X` using `mem_orth_iff.2 hzo`. Establish `hznX : F0.z ∉ F0.X`. Introduce `hzX`. Take `⟨c, hc⟩` from `exists_not_int (E := E)`. Establish `hcz : c • F0.z ∈ Lsub Λ (⟨F0, F0.z⟩ : LFlag S r T)`.

Use `Submodule.mem_inf.2 ⟨Submodule.mem_sup_right ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Submodule.restrictScalars_mem _ _ _).2 (F0.X.smul_mem c hzX)`. Conclude with `(Submodule.restrictScalars_mem _ _ _).2 ((orth S F0.X).smul_mem c hzorth)`. Take `⟨o, ho⟩` from `hprim c hcz`. Conclude with `hc o ho`.

Set `N : Submodule (𝓞 E) S.V` to `Formalism.L2.SG.Saturated.latSpan aa F0.e ⊔ Submodule.span (𝓞 E) {F0.z}`. Establish `hlatΛ : Formalism.L2.SG.Saturated.latSpan aa F0.e ≤ Λ` using `hXL ▸ inf_le_left`. Establish `hlatX : ∀ n ∈ Formalism.L2.SG.Saturated.latSpan aa F0.e, n ∈ F0.X`. Introduce `n hn`. Rewrite `hn` using `[← hXL]`.

Conclude with `(Submodule.restrictScalars_mem _ _ _).1 (Submodule.mem_inf.1 hn).2`. Establish `hNΛ : N ≤ Λ` using `sup_le hlatΛ ((Submodule.span_singleton_le_iff_mem _ _).2 hz)`. Establish `hzN : F0.z ∈ N` using `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Establish `hsat : ∀ (o : 𝓞 E) (x : S.V), o ≠ 0 → x ∈ Λ → o • x ∈ N → x ∈ N`. Introduce `o x ho hx hox`.

Take `⟨n1, hn1, n2, hn2, hsum⟩` from `Submodule.mem_sup.1 hox`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hn2`. Establish `hoE : (o : E) ≠ 0` using `(RingOfIntegers.coe_ne_zero_iff).2 ho`. Establish `hn1X : n1 ∈ F0.X` using `hlatX n1 hn1`. Establish `h1 : (o : E) • x = n1 + (t : E) • F0.z`.

Rewrite using `[← osmul, ← osmul, hsum]`. Establish `hxeq : x = (o : E)⁻¹ • n1 + ((o : E)⁻¹ * (t : E)) • F0.z`. Combine the equalities or inequalities in the displayed calculation. Establish `hxorth : x ∈ orth S F0.X`. Rewrite using `[hxeq]`.

Conclude with `add_mem ((orth S F0.X).smul_mem _ (hXo hn1X)) ((orth S F0.X).smul_mem _ hzorth)`. Establish `hcz : ((o : E)⁻¹ * (t : E)) • F0.z ∈ Lsub Λ (⟨F0, F0.z⟩ : LFlag S r T)`. Establish `he : ((o : E)⁻¹ * (t : E)) • F0.z = x + (-(o : E)⁻¹) • n1`. Rewrite using `[hxeq, neg_smul]`. Normalize the expressions using the abelian group laws.

Use `Submodule.mem_inf.2 ⟨?_, (Submodule.restrictScalars_mem _ _ _).2 ((orth S F0.X).smul_mem _ hzorth)⟩` and prove the remaining obligations. Rewrite using `[he]`. Use `Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨hx, ?_⟩) ?_` and prove the remaining obligations. Conclude with `(Submodule.restrictScalars_mem _ _ _).2 hxorth`. Conclude with `(Submodule.restrictScalars_mem _ _ _).2 (F0.X.smul_mem _ hn1X)`.

Take `⟨o', ho'⟩` from `hprim _ hcz`. Establish `hdiff : x - o' • F0.z ∈ Formalism.L2.SG.Saturated.latSpan aa F0.e`. Rewrite using `[← hXL]`. Use `Submodule.mem_inf.2 ⟨Λ.sub_mem hx (Λ.smul_mem o' hz), ?_⟩` and prove the remaining obligations. Use `(Submodule.restrictScalars_mem _ _ _).2 ?_` and prove the remaining obligations.

Establish `he : x - o' • F0.z = (o : E)⁻¹ • n1`. Rewrite using `[osmul, ho', hxeq]`. Normalize the expressions using the abelian group laws. Rewrite using `[he]`. Conclude with `F0.X.smul_mem _ hn1X`.

Establish `he : x = (x - o' • F0.z) + o' • F0.z` using `by abel`. Rewrite using `[he]`. Conclude with `Submodule.add_mem_sup hdiff (Submodule.mem_span_singleton.2 ⟨o', rfl⟩)`. Take `⟨ρ, hρN, hρid⟩` from `retraction_reduction E S.V Λ N hNΛ hlat.fg hsat`. Establish `hind : LinearIndependent E (Fin.snoc F0.e F0.z : Fin (r + 1) → S.V)` using `F0.e_indep.finSnoc hznX`.

Take `⟨cf, hcf⟩` from `dualFamilyExists E S.V (r + 1) _ hind`. Establish `hcfe : ∀ b a, cf (Fin.castSucc b) (F0.e a) = if b = a then 1 else 0`. Introduce `b a`. Establish `h` using `hcf (Fin.castSucc b) (Fin.castSucc a)`. Simplify using `only [Fin.snoc_castSucc, Fin.castSucc_inj] at h`.

Conclude with `h`. Establish `hcfz : ∀ b, cf (Fin.castSucc b) F0.z = 0`. Introduce `b`. Establish `h` using `hcf (Fin.castSucc b) (Fin.last r)`. Simplify using `only [Fin.snoc_last, Fin.castSucc_ne_last, if_false] at h`.

Conclude with `h`. Establish `hcfN : ∀ b, ∀ n ∈ N, cf (Fin.castSucc b) n ∈ aa b`. Introduce `b n hn`. Take `⟨n1, hn1, n2, hn2, rfl⟩` from `Submodule.mem_sup.1 hn`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hn2`.

Rewrite using `[map_add, osmul t, map_smul, hcfz, smul_zero, add_zero]`. Use `clear hn`. Proceed by induction on `hn1 using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, x, hx, rfl⟩` from `hy`.

Rewrite using `[map_smul, hcfe, smul_eq_mul]`. Use `split_ifs with hba`. Substitute `hba` using the available equality. Rewrite using `[mul_one]`. Conclude with `hx`.

Rewrite using `[mul_zero]`. Conclude with `fi_zero _`. Consider the case `zero => rw [map_zero]`. Conclude with `fi_zero _`. Consider the case `add y y' _ _ h1 h2 => rw [map_add]`.

Conclude with `fi_add h1 h2`. Consider the case `smul o y _ h1`. Rewrite using `[osmul o, map_smul, smul_eq_mul, ← Algebra.smul_def]`. Conclude with `fi_smul o h1`. Establish `hw` using `fun b : Fin r => sesquilinearRepresentation E S.V S.hT S.nondeg Λ hlat (((cf (Fin.castSucc b)).restrictScalars (𝓞 E)).comp ρ)`.

Use `choose f hf using hw`. Establish `hfv : ∀ b, ∀ x (hx : x ∈ Λ), S.hT (f b) x = cf (Fin.castSucc b) (ρ ⟨x, hx⟩)` using `fun b x hx => hf b ⟨x, hx⟩`. Use `⟨f, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b`. Establish `hne : (aa a : Submodule (𝓞 E) E) ≠ ⊥` using `FractionalIdeal.coeToSubmodule_ne_bot.2 (haa a)`.

Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Establish `hxa : x • F0.e a ∈ Formalism.L2.SG.Saturated.latSpan aa F0.e` using `Submodule.subset_span ⟨a, x, hx, rfl⟩`. Establish `h1` using `hfv b (x • F0.e a) (hlatΛ hxa)`. Rewrite `h1` using `[hρid ⟨_, hlatΛ hxa⟩ (Submodule.mem_sup_left hxa)]`. Simplify using `only [map_smul, hcfe, smul_eq_mul] at h1`.

Establish `h2 : S.hT (f b) (F0.e a) = if b = a then 1 else 0` using `mul_left_cancel₀ hx0 h1`. Establish `h3` using `S.herm.eq (f b) (F0.e a)`. Rewrite `h3` using `[h2]`. Rewrite using `[← h3]`. Use `split_ifs with h4 h5 h5`.

Simplify using the standard rewrite rules. Conclude with `absurd h4.symm h5`. Conclude with `absurd h5.symm h4`. Simplify using the standard rewrite rules. Introduce `b`.

Rewrite using `[hfv b F0.z hz, hρid ⟨F0.z, hz⟩ hzN]`. Conclude with `hcfz b`. Introduce `b x hx`. Rewrite using `[hfv b x hx]`. Conclude with `hcfN b _ (hρN _)`.
-/
theorem frame_reduction : FrameStep := by
  intro E _ _ _ S r T aa F0 Λ hC
  obtain ⟨hlat, huni, hz, hprim, hX, haa, hcs, htr⟩ := hC
  have hXL : Λ ⊓ (F0.X).restrictScalars (𝓞 E) = Formalism.L2.SG.Saturated.latSpan aa F0.e := hX
  have hzo : ∀ y ∈ F0.X, S.hT y F0.z = 0 := hX_left F0 F0.z_orth
  have hXo : F0.X ≤ orth S F0.X := X_le_orth F0
  have hzorth : F0.z ∈ orth S F0.X := mem_orth_iff.2 hzo

  have hznX : F0.z ∉ F0.X := by
    intro hzX
    obtain ⟨c, hc⟩ := exists_not_int (E := E)
    have hcz : c • F0.z ∈ Lsub Λ (⟨F0, F0.z⟩ : LFlag S r T) := by
      refine Submodule.mem_inf.2 ⟨Submodule.mem_sup_right ?_, ?_⟩
      · exact (Submodule.restrictScalars_mem _ _ _).2 (F0.X.smul_mem c hzX)
      · exact (Submodule.restrictScalars_mem _ _ _).2 ((orth S F0.X).smul_mem c hzorth)
    obtain ⟨o, ho⟩ := hprim c hcz
    exact hc o ho

  let N : Submodule (𝓞 E) S.V := Formalism.L2.SG.Saturated.latSpan aa F0.e ⊔ Submodule.span (𝓞 E) {F0.z}
  have hlatΛ : Formalism.L2.SG.Saturated.latSpan aa F0.e ≤ Λ := hXL ▸ inf_le_left
  have hlatX : ∀ n ∈ Formalism.L2.SG.Saturated.latSpan aa F0.e, n ∈ F0.X := by
    intro n hn
    rw [← hXL] at hn
    exact (Submodule.restrictScalars_mem _ _ _).1 (Submodule.mem_inf.1 hn).2
  have hNΛ : N ≤ Λ := sup_le hlatΛ ((Submodule.span_singleton_le_iff_mem _ _).2 hz)
  have hzN : F0.z ∈ N := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hsat : ∀ (o : 𝓞 E) (x : S.V), o ≠ 0 → x ∈ Λ → o • x ∈ N → x ∈ N := by
    intro o x ho hx hox
    obtain ⟨n1, hn1, n2, hn2, hsum⟩ := Submodule.mem_sup.1 hox
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hn2
    have hoE : (o : E) ≠ 0 := (RingOfIntegers.coe_ne_zero_iff).2 ho
    have hn1X : n1 ∈ F0.X := hlatX n1 hn1
    have h1 : (o : E) • x = n1 + (t : E) • F0.z := by
      rw [← osmul, ← osmul, hsum]
    have hxeq : x = (o : E)⁻¹ • n1 + ((o : E)⁻¹ * (t : E)) • F0.z := by
      calc x = (o : E)⁻¹ • ((o : E) • x) := by rw [smul_smul, inv_mul_cancel₀ hoE, one_smul]
        _ = _ := by rw [h1, smul_add, smul_smul]
    have hxorth : x ∈ orth S F0.X := by
      rw [hxeq]
      exact add_mem ((orth S F0.X).smul_mem _ (hXo hn1X)) ((orth S F0.X).smul_mem _ hzorth)
    have hcz : ((o : E)⁻¹ * (t : E)) • F0.z ∈ Lsub Λ (⟨F0, F0.z⟩ : LFlag S r T) := by
      have he : ((o : E)⁻¹ * (t : E)) • F0.z = x + (-(o : E)⁻¹) • n1 := by
        rw [hxeq, neg_smul]; abel
      refine Submodule.mem_inf.2 ⟨?_, (Submodule.restrictScalars_mem _ _ _).2
        ((orth S F0.X).smul_mem _ hzorth)⟩
      rw [he]
      refine Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨hx, ?_⟩) ?_
      · exact (Submodule.restrictScalars_mem _ _ _).2 hxorth
      · exact (Submodule.restrictScalars_mem _ _ _).2 (F0.X.smul_mem _ hn1X)
    obtain ⟨o', ho'⟩ := hprim _ hcz
    have hdiff : x - o' • F0.z ∈ Formalism.L2.SG.Saturated.latSpan aa F0.e := by
      rw [← hXL]
      refine Submodule.mem_inf.2 ⟨Λ.sub_mem hx (Λ.smul_mem o' hz), ?_⟩
      refine (Submodule.restrictScalars_mem _ _ _).2 ?_
      have he : x - o' • F0.z = (o : E)⁻¹ • n1 := by
        rw [osmul, ho', hxeq]; abel
      rw [he]
      exact F0.X.smul_mem _ hn1X
    have he : x = (x - o' • F0.z) + o' • F0.z := by abel
    rw [he]
    exact Submodule.add_mem_sup hdiff (Submodule.mem_span_singleton.2 ⟨o', rfl⟩)
  obtain ⟨ρ, hρN, hρid⟩ := retraction_reduction E S.V Λ N hNΛ hlat.fg hsat

  have hind : LinearIndependent E (Fin.snoc F0.e F0.z : Fin (r + 1) → S.V) :=
    F0.e_indep.finSnoc hznX
  obtain ⟨cf, hcf⟩ := dualFamilyExists E S.V (r + 1) _ hind
  have hcfe : ∀ b a, cf (Fin.castSucc b) (F0.e a) = if b = a then 1 else 0 := by
    intro b a
    have h := hcf (Fin.castSucc b) (Fin.castSucc a)
    simp only [Fin.snoc_castSucc, Fin.castSucc_inj] at h
    exact h
  have hcfz : ∀ b, cf (Fin.castSucc b) F0.z = 0 := by
    intro b
    have h := hcf (Fin.castSucc b) (Fin.last r)
    simp only [Fin.snoc_last, Fin.castSucc_ne_last, if_false] at h
    exact h
  have hcfN : ∀ b, ∀ n ∈ N, cf (Fin.castSucc b) n ∈ aa b := by
    intro b n hn
    obtain ⟨n1, hn1, n2, hn2, rfl⟩ := Submodule.mem_sup.1 hn
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hn2
    rw [map_add, osmul t, map_smul, hcfz, smul_zero, add_zero]
    clear hn
    induction hn1 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, x, hx, rfl⟩ := hy
      rw [map_smul, hcfe, smul_eq_mul]
      split_ifs with hba
      · subst hba; rw [mul_one]; exact hx
      · rw [mul_zero]; exact fi_zero _
    | zero => rw [map_zero]; exact fi_zero _
    | add y y' _ _ h1 h2 => rw [map_add]; exact fi_add h1 h2
    | smul o y _ h1 =>
      rw [osmul o, map_smul, smul_eq_mul, ← Algebra.smul_def]
      exact fi_smul o h1

  have hw := fun b : Fin r =>
    sesquilinearRepresentation E S.V S.hT S.nondeg Λ hlat (((cf (Fin.castSucc b)).restrictScalars (𝓞 E)).comp ρ)
  choose f hf using hw
  have hfv : ∀ b, ∀ x (hx : x ∈ Λ), S.hT (f b) x = cf (Fin.castSucc b) (ρ ⟨x, hx⟩) :=
    fun b x hx => hf b ⟨x, hx⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a b
    have hne : (aa a : Submodule (𝓞 E) E) ≠ ⊥ := FractionalIdeal.coeToSubmodule_ne_bot.2 (haa a)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hxa : x • F0.e a ∈ Formalism.L2.SG.Saturated.latSpan aa F0.e :=
      Submodule.subset_span ⟨a, x, hx, rfl⟩
    have h1 := hfv b (x • F0.e a) (hlatΛ hxa)
    rw [hρid ⟨_, hlatΛ hxa⟩ (Submodule.mem_sup_left hxa)] at h1
    simp only [map_smul, hcfe, smul_eq_mul] at h1
    have h2 : S.hT (f b) (F0.e a) = if b = a then 1 else 0 := mul_left_cancel₀ hx0 h1
    have h3 := S.herm.eq (f b) (F0.e a)
    rw [h2] at h3
    rw [← h3]
    split_ifs with h4 h5 h5
    · simp
    · exact absurd h4.symm h5
    · exact absurd h5.symm h4
    · simp
  · intro b
    rw [hfv b F0.z hz, hρid ⟨F0.z, hz⟩ hzN]
    exact hcfz b
  · intro b x hx
    rw [hfv b x hx]
    exact hcfN b _ (hρN _)

end PI.SRW
