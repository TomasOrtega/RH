import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Formalism.SharpRestriction.LevelLetterCocycles.WildPro

namespace GlobalTheory.CompanionTheory.RelSym

section Grp

variable {G : Type*} [Group G]

/- English proof (translation)
Rewrite using `[← Subgroup.commutator_eq_bot_iff_le_centralizer, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']`.
-/
theorem commutator_le_of_map {N : Subgroup G} [N.Normal] {X Y : Subgroup G} :
    ⁅X, Y⁆ ≤ N ↔ X.map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer (Y.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← Subgroup.map_commutator,
    Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

/- English proof (translation)
Rewrite `hA`, `hB`, `hAB`, the goal using `[commutator_le_of_map]`. Rewrite using `[Subgroup.map_sup]`. Establish `hBA` using `Subgroup.le_centralizer_iff.mp hAB`. Establish `h1 : A.map (QuotientGroup.mk' N) ⊔ B.map (QuotientGroup.mk' N) ≤ Subgroup.centralizer (A.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N))` using `sup_le hA hBA`. Establish `h2 : A.map (QuotientGroup.mk' N) ⊔ B.map (QuotientGroup.mk' N) ≤ Subgroup.centralizer (B.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N))` using `sup_le hAB hB`.

Establish `h3` using `Subgroup.le_centralizer_iff.mp h1`. Establish `h4` using `Subgroup.le_centralizer_iff.mp h2`. Conclude with `Subgroup.le_centralizer_iff.mp (sup_le h3 h4)`.
-/
theorem comm_sup {N : Subgroup G} [N.Normal] {A B : Subgroup G} (hA : ⁅A, A⁆ ≤ N) (hB : ⁅B, B⁆ ≤ N)
    (hAB : ⁅A, B⁆ ≤ N) : ⁅A ⊔ B, A ⊔ B⁆ ≤ N := by
  rw [commutator_le_of_map] at hA hB hAB ⊢
  rw [Subgroup.map_sup]
  have hBA := Subgroup.le_centralizer_iff.mp hAB
  have h1 : A.map (QuotientGroup.mk' N) ⊔ B.map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer (A.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) := sup_le hA hBA
  have h2 : A.map (QuotientGroup.mk' N) ⊔ B.map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer (B.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) := sup_le hAB hB
  have h3 := Subgroup.le_centralizer_iff.mp h1
  have h4 := Subgroup.le_centralizer_iff.mp h2
  exact Subgroup.le_centralizer_iff.mp (sup_le h3 h4)

/- English proof (translation)
Rewrite `hX`, `hY`, the goal using `[commutator_le_of_map]`. Rewrite using `[Subgroup.map_sup]`. Conclude with `Subgroup.le_centralizer_iff.mp (sup_le (Subgroup.le_centralizer_iff.mp hX) (Subgroup.le_centralizer_iff.mp hY))`.
-/
theorem comm_right_sup {N : Subgroup G} [N.Normal] {A X Y : Subgroup G} (hX : ⁅A, X⁆ ≤ N)
    (hY : ⁅A, Y⁆ ≤ N) : ⁅A, X ⊔ Y⁆ ≤ N := by
  rw [commutator_le_of_map] at hX hY ⊢
  rw [Subgroup.map_sup]
  exact Subgroup.le_centralizer_iff.mp
    (sup_le (Subgroup.le_centralizer_iff.mp hX) (Subgroup.le_centralizer_iff.mp hY))

/- English proof (translation)
Rewrite using `[Subgroup.commutator_eq_bot_iff_le_centralizer]`. Introduce `a ha`. Rewrite using `[Subgroup.mem_centralizer_iff]`. Introduce `b hb`. Take `⟨m, rfl⟩` from `Subgroup.mem_zpowers_iff.mp ha`.

Take `⟨n, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hb`. Conclude with `(Commute.refl g).zpow_zpow n m`.
-/
theorem commutator_zpowers_self (g : G) : ⁅Subgroup.zpowers g, Subgroup.zpowers g⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.refl g).zpow_zpow n m

/- English proof (translation)
Take `⟨n, hn⟩` from `nilpotent_iff_lowerCentralSeries.mp (inferInstance : Group.IsNilpotent Q)`. Establish `key : ∀ m, R (C ⊔ (⊤ : Subgroup Q).lowerCentralSeries m)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simpa using h0`.

Consider the case `succ m ih`. Use `hs _ _ ih le_sup_left (sup_le_sup_left (lowerCentralSeries_antitone _ (Nat.le_succ m)) _) ?_` and prove the remaining obligations. Establish `hL : ⁅(⊤ : Subgroup Q).lowerCentralSeries m, ⊤⁆ ≤ (⊤ : Subgroup Q).lowerCentralSeries (m + 1)` using `(lowerCentralSeries_succ _ _).ge`. Use `le_trans (comm_sup (N := (⊤ : Subgroup Q).lowerCentralSeries (m + 1)) ?_ ?_ ?_) le_sup_right` and prove the remaining obligations. Rewrite using `[hC]`.

Conclude with `bot_le`. Conclude with `le_trans (Subgroup.commutator_mono le_rfl le_top) hL`. Rewrite using `[Subgroup.commutator_comm]`. Conclude with `le_trans (Subgroup.commutator_mono le_rfl le_top) hL`. Simplify `key n` using `[hn]`.
-/
theorem chain_nilpotent {Q : Type*} [Group Q] [Group.IsNilpotent Q] (C : Subgroup Q)
    (hC : ⁅C, C⁆ = ⊥) (R : Subgroup Q → Prop) (h0 : R ⊤)
    (hs : ∀ D D' : Subgroup Q, R D → C ≤ D' → D' ≤ D → ⁅D, D⁆ ≤ D' → R D') : R C := by
  obtain ⟨n, hn⟩ := nilpotent_iff_lowerCentralSeries.mp (inferInstance : Group.IsNilpotent Q)
  have key : ∀ m, R (C ⊔ (⊤ : Subgroup Q).lowerCentralSeries m) := by
    intro m
    induction m with
    | zero => simpa using h0
    | succ m ih =>
      refine hs _ _ ih le_sup_left (sup_le_sup_left (lowerCentralSeries_antitone _ (Nat.le_succ m)) _) ?_
      have hL : ⁅(⊤ : Subgroup Q).lowerCentralSeries m, ⊤⁆ ≤
          (⊤ : Subgroup Q).lowerCentralSeries (m + 1) := (lowerCentralSeries_succ _ _).ge
      refine le_trans (comm_sup (N := (⊤ : Subgroup Q).lowerCentralSeries (m + 1)) ?_ ?_ ?_) le_sup_right
      · rw [hC]; exact bot_le
      · exact le_trans (Subgroup.commutator_mono le_rfl le_top) hL
      · rw [Subgroup.commutator_comm]
        exact le_trans (Subgroup.commutator_mono le_rfl le_top) hL
  simpa [hn] using key n

end Grp

end GlobalTheory.CompanionTheory.RelSym

namespace GlobalTheory.CompanionTheory.RelSym

section Core

open scoped commutatorElement

variable {G : Type*} [Group G]

/- English proof (translation)
Establish `hk : (QuotientGroup.mk' C).ker = C` using `QuotientGroup.ker_mk' C`. Establish `hC : C.map (QuotientGroup.mk' C) = ⊥`. Rewrite using `[Subgroup.map_eq_bot_iff, hk]`. Establish `e : (H' ⊔ C) = (H'.map (QuotientGroup.mk' C)).comap (QuotientGroup.mk' C)`. Rewrite using `[Subgroup.comap_map_eq, hk]`.

Rewrite using `[e, ← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator, Subgroup.map_sup, hC, sup_bot_eq, ← Subgroup.map_commutator]`. Rewrite `h` using `[e, ← Subgroup.map_le_iff_le_comap]`. Conclude with `h`.
-/
theorem commutator_sup_normal {C H H' : Subgroup G} [C.Normal] (h : ⁅H, H⁆ ≤ H' ⊔ C) :
    ⁅H ⊔ C, H ⊔ C⁆ ≤ H' ⊔ C := by
  have hk : (QuotientGroup.mk' C).ker = C := QuotientGroup.ker_mk' C
  have hC : C.map (QuotientGroup.mk' C) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hk]
  have e : (H' ⊔ C) = (H'.map (QuotientGroup.mk' C)).comap (QuotientGroup.mk' C) := by
    rw [Subgroup.comap_map_eq, hk]
  rw [e, ← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator, Subgroup.map_sup, hC, sup_bot_eq,
    ← Subgroup.map_commutator]
  rw [e, ← Subgroup.map_le_iff_le_comap] at h
  exact h

/- English proof (translation)
Establish `: (K.subgroupOf I).FiniteIndex` using `⟨hfin⟩`. Establish `hf : Finite (↥I ⧸ K.subgroupOf I)` using `Subgroup.finite_quotient_of_finiteIndex`. Set `f : (↥I ⧸ K.subgroupOf I) → ↥(I.map (QuotientGroup.mk' K))` to `Quotient.lift (fun i : ↥I => (⟨QuotientGroup.mk' K i.1, i.1, i.2, rfl⟩ : ↥(I.map (QuotientGroup.mk' K)))) (by`. Introduce `a b hab`. Establish `hab'` using `QuotientGroup.leftRel_apply.mp hab`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show (QuotientGroup.mk a.1 : G ⧸ K) = QuotientGroup.mk b.1`. Rewrite using `[QuotientGroup.eq]`. Conclude with `hab')`. Use `Finite.of_surjective f ?_` and prove the remaining obligations.

Introduce and unpack `⟨_, i, hi, rfl⟩`. Conclude with `⟨QuotientGroup.mk ⟨i, hi⟩, rfl⟩`.
-/
theorem finiteIndex_quot_of_relIndex {K I : Subgroup G} [K.Normal] (hKI : K ≤ I)
    (hfin : K.relIndex I ≠ 0) : Finite ↥(I.map (QuotientGroup.mk' K)) := by
  have : (K.subgroupOf I).FiniteIndex := ⟨hfin⟩
  have hf : Finite (↥I ⧸ K.subgroupOf I) := Subgroup.finite_quotient_of_finiteIndex
  let f : (↥I ⧸ K.subgroupOf I) → ↥(I.map (QuotientGroup.mk' K)) :=
    Quotient.lift (fun i : ↥I => (⟨QuotientGroup.mk' K i.1, i.1, i.2, rfl⟩ : ↥(I.map (QuotientGroup.mk' K))))
      (by
        intro a b hab
        have hab' := QuotientGroup.leftRel_apply.mp hab
        apply Subtype.ext
        show (QuotientGroup.mk a.1 : G ⧸ K) = QuotientGroup.mk b.1
        rw [QuotientGroup.eq]
        exact hab')
  refine Finite.of_surjective f ?_
  rintro ⟨_, i, hi, rfl⟩
  exact ⟨QuotientGroup.mk ⟨i, hi⟩, rfl⟩

/- English proof (translation)
Establish `hIK : (I.map (QuotientGroup.mk' K)).Normal` using `Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective K)`. Establish `hfinI` using `finiteIndex_quot_of_relIndex hKI hfin`. Set `f : G →* MulAut ↥(I.map (QuotientGroup.mk' K))` to `(MulAut.conjNormal).comp (QuotientGroup.mk' K)`. Establish `hfinA : Finite (MulAut ↥(I.map (QuotientGroup.mk' K)))` using `Finite.of_injective (fun e => e.toEquiv) (fun a b hab => by`. Use extensionality with `x`.

Conclude with `congrArg (fun e : _ ≃ _ => (e x).1) hab)`. Establish `hcomm : ∀ c ∈ f.ker, ∀ i ∈ I, ⁅i, c⁆ ∈ K`. Introduce `c hc i hi`. Establish `h1 : f c = 1` using `hc`. Establish `h2` using `congrArg (fun e : MulAut ↥(I.map (QuotientGroup.mk' K)) => ((e ⟨QuotientGroup.mk' K i, i, hi, rfl⟩ : ↥(I.map (QuotientGroup.mk' K))) : G ⧸ K)) h1`.

Simplify using `only [f, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply] at h2`. Rewrite using `[← QuotientGroup.eq_one_iff, commutatorElement_def]`. Establish `h3 : (c : G ⧸ K) * (i : G ⧸ K) * (c : G ⧸ K)⁻¹ = (i : G ⧸ K)` using `h2`. Establish `h4 : ∀ a b : G ⧸ K, b * a * b⁻¹ = a → a * b * a⁻¹ * b⁻¹ = 1`. Introduce `a b h`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `using h4 _ _ h3`. Use `⟨f.ker, inferInstance, inferInstance, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k hk`. Establish `: QuotientGroup.mk' K k = 1` using `by simpa using hk`.

Use `show MulAut.conjNormal (QuotientGroup.mk' K k) = 1`. Rewrite using `[this, map_one]`. Rewrite using `[Subgroup.commutator_le]`. Introduce `i hi c hc`. Conclude with `hcomm c hc i hi`.

Establish `hcyc : IsCyclic (G ⧸ I)`. Use `⟨(ψ : G ⧸ I), fun x => ?_⟩` and prove the remaining obligations. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective x`. Take `⟨n, hn⟩` from `hψ g`. Use `⟨-n, ?_⟩` and prove the remaining obligations.

Use `show (ψ : G ⧸ I) ^ (-n) = (g : G ⧸ I)`. Establish `h1 : ((g * ψ ^ n : G) : G ⧸ I) = 1` using `(QuotientGroup.eq_one_iff _).mpr hn`. Rewrite `h1` using `[QuotientGroup.mk_mul, QuotientGroup.mk_zpow]`. Rewrite using `[zpow_neg]`. Conclude with `inv_eq_of_mul_eq_one_left h1`.

Set `X` to `f.ker.map (QuotientGroup.mk' K)`. Set `g' : ↥X →* G ⧸ I` to `(QuotientGroup.map K I (MonoidHom.id G) hKI).comp X.subtype`. Establish `hc : g'.ker ≤ Subgroup.center ↥X`. Introduce and unpack `⟨_, a, ha, rfl⟩ hx`. Establish `haI : a ∈ I` using `(QuotientGroup.eq_one_iff _).mp hx`.

Rewrite using `[Subgroup.mem_center_iff]`. Introduce and unpack `⟨_, b, hb, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1` using `(QuotientGroup.eq_one_iff _).mpr (hcomm b hb a haI)`. Rewrite `h1` using `[commutatorElement_def]`.

Use `show (QuotientGroup.mk' K b) * (QuotientGroup.mk' K a) = (QuotientGroup.mk' K a) * (QuotientGroup.mk' K b)`. Establish `h2 : ∀ u v : G ⧸ K, u * v * u⁻¹ * v⁻¹ = 1 → v * u = u * v`. Introduce `u v h`. Combine the equalities or inequalities in the displayed calculation. Conclude with `h2 _ _ (by simpa using h1)`.

Establish `hab` using `commutative_of_cyclic_center_quotient g' hc`. Rewrite using `[Subgroup.commutator_le]`. Introduce `a ha b hb`. Establish `h1` using `hab ⟨QuotientGroup.mk' K a, a, ha, rfl⟩ ⟨QuotientGroup.mk' K b, b, hb, rfl⟩`. Establish `h2 : (a : G ⧸ K) * (b : G ⧸ K) = (b : G ⧸ K) * (a : G ⧸ K)` using `congrArg Subtype.val h1`.

Rewrite using `[← QuotientGroup.eq_one_iff, commutatorElement_def]`. Establish `h3 : ∀ u v : G ⧸ K, u * v = v * u → u * v * u⁻¹ * v⁻¹ = 1`. Introduce `u v h`. Rewrite using `[h]`. Use `group`.

Simplify using `using h3 _ _ h2`.
-/
theorem exists_centraliser {K I : Subgroup G} [K.Normal] [I.Normal] (hKI : K ≤ I)
    (hfin : K.relIndex I ≠ 0) (ψ : G) (hψ : ∀ g : G, ∃ n : ℤ, g * ψ ^ n ∈ I) :
    ∃ C : Subgroup G, C.Normal ∧ C.FiniteIndex ∧ K ≤ C ∧ ⁅I, C⁆ ≤ K ∧ ⁅C, C⁆ ≤ K := by
  classical
  have hIK : (I.map (QuotientGroup.mk' K)).Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective K)
  have hfinI := finiteIndex_quot_of_relIndex hKI hfin
  let f : G →* MulAut ↥(I.map (QuotientGroup.mk' K)) := (MulAut.conjNormal).comp (QuotientGroup.mk' K)
  have hfinA : Finite (MulAut ↥(I.map (QuotientGroup.mk' K))) :=
    Finite.of_injective (fun e => e.toEquiv) (fun a b hab => by
      ext x
      exact congrArg (fun e : _ ≃ _ => (e x).1) hab)
  have hcomm : ∀ c ∈ f.ker, ∀ i ∈ I, ⁅i, c⁆ ∈ K := by
    intro c hc i hi
    have h1 : f c = 1 := hc
    have h2 := congrArg (fun e : MulAut ↥(I.map (QuotientGroup.mk' K)) =>
      ((e ⟨QuotientGroup.mk' K i, i, hi, rfl⟩ : ↥(I.map (QuotientGroup.mk' K))) : G ⧸ K)) h1
    simp only [f, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply] at h2
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
    have h3 : (c : G ⧸ K) * (i : G ⧸ K) * (c : G ⧸ K)⁻¹ = (i : G ⧸ K) := h2
    have h4 : ∀ a b : G ⧸ K, b * a * b⁻¹ = a → a * b * a⁻¹ * b⁻¹ = 1 := by
      intro a b h
      calc a * b * a⁻¹ * b⁻¹ = a * (b * a * b⁻¹)⁻¹ := by group
        _ = 1 := by rw [h]; simp
    simpa using h4 _ _ h3
  refine ⟨f.ker, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro k hk
    have : QuotientGroup.mk' K k = 1 := by simpa using hk
    show MulAut.conjNormal (QuotientGroup.mk' K k) = 1
    rw [this, map_one]
  · rw [Subgroup.commutator_le]
    intro i hi c hc
    exact hcomm c hc i hi
  · have hcyc : IsCyclic (G ⧸ I) := by
      refine ⟨(ψ : G ⧸ I), fun x => ?_⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨n, hn⟩ := hψ g
      refine ⟨-n, ?_⟩
      show (ψ : G ⧸ I) ^ (-n) = (g : G ⧸ I)
      have h1 : ((g * ψ ^ n : G) : G ⧸ I) = 1 := (QuotientGroup.eq_one_iff _).mpr hn
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
      rw [zpow_neg]
      exact inv_eq_of_mul_eq_one_left h1
    let X := f.ker.map (QuotientGroup.mk' K)
    let g' : ↥X →* G ⧸ I := (QuotientGroup.map K I (MonoidHom.id G) hKI).comp X.subtype
    have hc : g'.ker ≤ Subgroup.center ↥X := by
      rintro ⟨_, a, ha, rfl⟩ hx
      have haI : a ∈ I := (QuotientGroup.eq_one_iff _).mp hx
      rw [Subgroup.mem_center_iff]
      rintro ⟨_, b, hb, rfl⟩
      apply Subtype.ext
      have h1 := (QuotientGroup.eq_one_iff _).mpr (hcomm b hb a haI)
      rw [commutatorElement_def] at h1
      show (QuotientGroup.mk' K b) * (QuotientGroup.mk' K a) = (QuotientGroup.mk' K a) * (QuotientGroup.mk' K b)
      have h2 : ∀ u v : G ⧸ K, u * v * u⁻¹ * v⁻¹ = 1 → v * u = u * v := by
        intro u v h
        calc v * u = (u * v * u⁻¹ * v⁻¹)⁻¹ * (u * v) := by group
          _ = u * v := by rw [h]; simp
      exact h2 _ _ (by simpa using h1)
    have hab := commutative_of_cyclic_center_quotient g' hc
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h1 := hab ⟨QuotientGroup.mk' K a, a, ha, rfl⟩ ⟨QuotientGroup.mk' K b, b, hb, rfl⟩
    have h2 : (a : G ⧸ K) * (b : G ⧸ K) = (b : G ⧸ K) * (a : G ⧸ K) := congrArg Subtype.val h1
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
    have h3 : ∀ u v : G ⧸ K, u * v = v * u → u * v * u⁻¹ * v⁻¹ = 1 := by
      intro u v h
      rw [h]; group
    simpa using h3 _ _ h2

end Core

end GlobalTheory.CompanionTheory.RelSym

namespace GlobalTheory.CompanionTheory.RelSym

section Core3

open scoped commutatorElement

variable {G : Type*} [Group G]

/- English proof (translation)
Establish `: Fact p.Prime` using `⟨hp⟩`. Take `⟨C, hCn, hCf, hKC, hIC, hCC⟩` from `exists_centraliser hKI hfin ψ hψ`. Establish `hrelfin : ∀ U V : Subgroup G, C ≤ U → U.relIndex V ≠ 0`. Introduce `U V hU`. Establish `: U.FiniteIndex` using `Subgroup.finiteIndex_of_le hU`.

Conclude with `(inferInstance : (U.subgroupOf V).FiniteIndex).index_ne_zero`. Establish `hsup : I ⊔ Subgroup.zpowers ψ = ⊤`. Use `eq_top_iff.mpr fun g _ => ?_` and prove the remaining obligations. Take `⟨n, hn⟩` from `hψ g`. Use `Subgroup.mul_mem_sup hn (Subgroup.mem_zpowers (ψ ^ n)⁻¹ |> fun _ => (Subgroup.zpowers ψ).inv_mem (Subgroup.zpow_mem_zpowers ψ n))` as an intermediate fact.

Simplify using `using this`. Establish `hIcomm : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ I`. Rewrite using `[← hsup]`. Use `comm_sup (Subgroup.commutator_le_self I) ?_ ?_` and prove the remaining obligations. Rewrite using `[commutator_zpowers_self]`.

Conclude with `bot_le`. Conclude with `Subgroup.commutator_le_left _ _`. Establish `hstepS : ∀ H H' : Subgroup G, Sb (H ⊔ C) → H' ≤ H → ⁅H, H⁆ ≤ H' ⊔ C → Sb (H' ⊔ C)`. Introduce `H H' hS hle hc`. Conclude with `step _ _ hS (sup_le_sup_right hle _) (commutator_sup_normal hc) (hrelfin _ _ le_sup_right) (hKC.trans le_sup_right)`.

Establish `hSI : Sb (I ⊔ C)`. Use `hstepS ⊤ I (by simpa using h0) le_top (hIcomm.trans le_sup_left)` and prove the remaining obligations. Establish `hPK : ⁅I, I⁆ ≤ P ⊔ K`. Establish `hn : (P ⊔ K).Normal` using `inferInstance`. Use `le_trans (Subgroup.commutator_mono ht ht) (comm_sup ?_ ?_ ?_)` and prove the remaining obligations.

Rewrite using `[commutator_zpowers_self]`. Conclude with `bot_le`. Conclude with `Subgroup.commutator_le_self _`. Conclude with `Subgroup.commutator_le_right _ _`. Establish `hSP : Sb (P ⊔ C)`.

Use `hstepS I P hSI hPI (hPK.trans ?_)` and prove the remaining obligations. Conclude with `sup_le_sup_left hKC _`. Establish `hwild : ∀ g ∈ P, g ∈ kx → g ∈ ky`. Introduce `g hg hgx`. Establish `hfq : Finite (G ⧸ C)` using `Subgroup.finite_quotient_of_finiteIndex`.

Establish `hpg : IsPGroup p ↥(P.map (QuotientGroup.mk' C))`. Introduce and unpack `⟨_, a, ha, rfl⟩`. Take `⟨k, hk⟩` from `hpK a ha`. Use `⟨k, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (QuotientGroup.mk' C a) ^ p ^ k = 1`.

Rewrite using `[← map_pow]`. Conclude with `(QuotientGroup.eq_one_iff _).mpr (hKC hk)`. Establish `hnil : Group.IsNilpotent ↥(P.map (QuotientGroup.mk' C))` using `hpg.isNilpotent`. Set `s` to `(P.map (QuotientGroup.mk' C)).subtype`. Set `c : ↥(P.map (QuotientGroup.mk' C))` to `⟨QuotientGroup.mk' C g, g, hg, rfl⟩`.

Set `R : Subgroup ↥(P.map (QuotientGroup.mk' C)) → Prop` to `fun D => Sb ((D.map s).comap (QuotientGroup.mk' C))`. Establish `hC' : ∀ D : Subgroup ↥(P.map (QuotientGroup.mk' C)), C ≤ (D.map s).comap (QuotientGroup.mk' C)`. Introduce `D a ha`. Use `show QuotientGroup.mk' C a ∈ D.map s`. Rewrite using `[show QuotientGroup.mk' C a = 1 from (QuotientGroup.eq_one_iff _).mpr ha]`.

Conclude with `one_mem _`. Establish `hR : R (Subgroup.zpowers c)`. Use `chain_nilpotent (Subgroup.zpowers c) (commutator_zpowers_self c) R ?_ ?_` and prove the remaining obligations. Use `show Sb (((⊤ : Subgroup _).map s).comap (QuotientGroup.mk' C))`. Rewrite using `[← MonoidHom.range_eq_map, Subgroup.range_subtype, Subgroup.comap_map_eq, QuotientGroup.ker_mk']`.

Conclude with `hSP`. Introduce `D D' hD _ hle hc`. Use `step _ _ hD (Subgroup.comap_mono (Subgroup.map_mono hle)) ?_ (hrelfin _ _ (hC' D')) (hKC.trans (hC' D'))` and prove the remaining obligations. Rewrite using `[← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hV : ((Subgroup.zpowers c).map s).comap (QuotientGroup.mk' C) ≤ Subgroup.zpowers g ⊔ C`. Introduce `v hv`. Take `⟨x, hx', e⟩` from `hv`. Take `⟨n, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hx'`. Establish `e2 : ((g ^ n : G) : G ⧸ C) = (v : G ⧸ C)`.

Establish `e' : (QuotientGroup.mk' C g) ^ n = QuotientGroup.mk' C v`. Establish `e3` using `e`. Rewrite `e3` using `[map_zpow]`. Conclude with `e3`. Use `show QuotientGroup.mk' C (g ^ n) = QuotientGroup.mk' C v`.

Rewrite using `[map_zpow]`. Conclude with `e'`. Establish `h3 : (g ^ n)⁻¹ * v ∈ C` using `QuotientGroup.eq.mp e2`. Use `Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers g n) h3` as an intermediate fact. Simplify using `using this`.

Use `hrel _ hR ?_ g ⟨c, Subgroup.mem_zpowers c, rfl⟩ hgx` and prove the remaining obligations. Use `le_trans (Subgroup.commutator_mono hV hV) (le_trans (comm_sup (N := K) ?_ hCC ?_) hKy)` and prove the remaining obligations. Rewrite using `[commutator_zpowers_self]`. Conclude with `bot_le`. Establish `hgI : Subgroup.zpowers g ≤ I`.

Rewrite using `[Subgroup.zpowers_le]`. Conclude with `hPI hg`. Conclude with `le_trans (Subgroup.commutator_mono hgI le_rfl) hIC`. Establish `hB : ⁅(⊤ : Subgroup G), P⁆ ≤ ky`. Rewrite using `[Subgroup.commutator_le]`.

Introduce `u _ g hg`. Conclude with `hwild _ (Subgroup.commutator_le_right ⊤ P (Subgroup.commutator_mem_commutator trivial hg)) (hx (Subgroup.commutator_mem_commutator trivial trivial))`. Establish `hK : ⁅(⊤ : Subgroup G), K⁆ ≤ ky` using `(Subgroup.commutator_le_right _ _).trans hKy`. Establish `hPKy : ⁅(⊤ : Subgroup G), P ⊔ K⁆ ≤ ky` using `comm_right_sup hB hK`. Establish `hII : ⁅I, I⁆ ≤ ky`.

Use `le_trans (Subgroup.commutator_mono ht ht) (comm_sup ?_ ?_ ?_)` and prove the remaining obligations. Rewrite using `[commutator_zpowers_self]`. Conclude with `bot_le`. Conclude with `le_trans (Subgroup.commutator_mono le_top le_rfl) hPKy`. Conclude with `le_trans (Subgroup.commutator_mono le_top le_rfl) hPKy`.

Establish `hIC' : ⁅I ⊔ C, I ⊔ C⁆ ≤ ky` using `comm_sup hII (hCC.trans hKy) (hIC.trans hKy)`. Establish `hE : ⁅(⊤ : Subgroup G), I⁆ ≤ ky`. Rewrite using `[Subgroup.commutator_le]`. Introduce `u _ g hg`. Conclude with `hrel _ hSI hIC' _ (le_sup_left (a := I) (Subgroup.commutator_le_right ⊤ I (Subgroup.commutator_mem_commutator trivial hg))) (hx (Subgroup.commutator_mem_commutator trivial trivial))`.

Rewrite using `[← hsup]`. Use `comm_sup hII ?_ ?_` and prove the remaining obligations. Rewrite using `[commutator_zpowers_self]`. Conclude with `bot_le`. Rewrite using `[Subgroup.commutator_comm]`.

Conclude with `le_trans (Subgroup.commutator_mono le_top le_rfl) hE`.
-/
theorem core {p : ℕ} (hp : p.Prime) (K I P kx ky : Subgroup G) [K.Normal] [I.Normal] [P.Normal]
    [kx.Normal] [ky.Normal] (hKI : K ≤ I) (hPI : P ≤ I) (hfin : K.relIndex I ≠ 0) (ψ t : G)
    (hψ : ∀ g : G, ∃ n : ℤ, g * ψ ^ n ∈ I) (ht : I ≤ Subgroup.zpowers t ⊔ (P ⊔ K))
    (hpK : ∀ g ∈ P, ∃ k : ℕ, g ^ p ^ k ∈ K) (hKy : K ≤ ky)
    (Sb : Subgroup G → Prop) (h0 : Sb ⊤)
    (step : ∀ U V : Subgroup G, Sb V → U ≤ V → ⁅V, V⁆ ≤ U → U.relIndex V ≠ 0 → K ≤ U → Sb U)
    (hrel : ∀ V, Sb V → ⁅V, V⁆ ≤ ky → ∀ g ∈ V, g ∈ kx → g ∈ ky)
    (hx : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ kx) : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ ky := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨C, hCn, hCf, hKC, hIC, hCC⟩ := exists_centraliser hKI hfin ψ hψ
  have hrelfin : ∀ U V : Subgroup G, C ≤ U → U.relIndex V ≠ 0 := by
    intro U V hU
    have : U.FiniteIndex := Subgroup.finiteIndex_of_le hU
    exact (inferInstance : (U.subgroupOf V).FiniteIndex).index_ne_zero
  have hsup : I ⊔ Subgroup.zpowers ψ = ⊤ := by
    refine eq_top_iff.mpr fun g _ => ?_
    obtain ⟨n, hn⟩ := hψ g
    have := Subgroup.mul_mem_sup hn (Subgroup.mem_zpowers (ψ ^ n)⁻¹ |> fun _ =>
      (Subgroup.zpowers ψ).inv_mem (Subgroup.zpow_mem_zpowers ψ n))
    simpa using this
  have hIcomm : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ I := by
    rw [← hsup]
    refine comm_sup (Subgroup.commutator_le_self I) ?_ ?_
    · rw [commutator_zpowers_self]; exact bot_le
    · exact Subgroup.commutator_le_left _ _
  have hstepS : ∀ H H' : Subgroup G, Sb (H ⊔ C) → H' ≤ H → ⁅H, H⁆ ≤ H' ⊔ C → Sb (H' ⊔ C) := by
    intro H H' hS hle hc
    exact step _ _ hS (sup_le_sup_right hle _) (commutator_sup_normal hc)
      (hrelfin _ _ le_sup_right) (hKC.trans le_sup_right)
  have hSI : Sb (I ⊔ C) := by
    refine hstepS ⊤ I (by simpa using h0) le_top (hIcomm.trans le_sup_left)
  have hPK : ⁅I, I⁆ ≤ P ⊔ K := by
    have hn : (P ⊔ K).Normal := inferInstance
    refine le_trans (Subgroup.commutator_mono ht ht) (comm_sup ?_ ?_ ?_)
    · rw [commutator_zpowers_self]; exact bot_le
    · exact Subgroup.commutator_le_self _
    · exact Subgroup.commutator_le_right _ _
  have hSP : Sb (P ⊔ C) := by
    refine hstepS I P hSI hPI (hPK.trans ?_)
    exact sup_le_sup_left hKC _
  have hwild : ∀ g ∈ P, g ∈ kx → g ∈ ky := by
    intro g hg hgx
    have hfq : Finite (G ⧸ C) := Subgroup.finite_quotient_of_finiteIndex
    have hpg : IsPGroup p ↥(P.map (QuotientGroup.mk' C)) := by
      rintro ⟨_, a, ha, rfl⟩
      obtain ⟨k, hk⟩ := hpK a ha
      refine ⟨k, Subtype.ext ?_⟩
      show (QuotientGroup.mk' C a) ^ p ^ k = 1
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hKC hk)
    have hnil : Group.IsNilpotent ↥(P.map (QuotientGroup.mk' C)) := hpg.isNilpotent
    let s := (P.map (QuotientGroup.mk' C)).subtype
    let c : ↥(P.map (QuotientGroup.mk' C)) := ⟨QuotientGroup.mk' C g, g, hg, rfl⟩
    let R : Subgroup ↥(P.map (QuotientGroup.mk' C)) → Prop :=
      fun D => Sb ((D.map s).comap (QuotientGroup.mk' C))
    have hC' : ∀ D : Subgroup ↥(P.map (QuotientGroup.mk' C)), C ≤ (D.map s).comap (QuotientGroup.mk' C) := by
      intro D a ha
      show QuotientGroup.mk' C a ∈ D.map s
      rw [show QuotientGroup.mk' C a = 1 from (QuotientGroup.eq_one_iff _).mpr ha]
      exact one_mem _
    have hR : R (Subgroup.zpowers c) := by
      refine chain_nilpotent (Subgroup.zpowers c) (commutator_zpowers_self c) R ?_ ?_
      · show Sb (((⊤ : Subgroup _).map s).comap (QuotientGroup.mk' C))
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype, Subgroup.comap_map_eq,
          QuotientGroup.ker_mk']
        exact hSP
      · intro D D' hD _ hle hc
        refine step _ _ hD (Subgroup.comap_mono (Subgroup.map_mono hle)) ?_ (hrelfin _ _ (hC' D'))
          (hKC.trans (hC' D'))
        rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator]
        calc _ ≤ ⁅D.map s, D.map s⁆ := Subgroup.commutator_mono (Subgroup.map_comap_le _ _) (Subgroup.map_comap_le _ _)
          _ = (⁅D, D⁆).map s := (Subgroup.map_commutator _ _ _).symm
          _ ≤ D'.map s := Subgroup.map_mono hc
    have hV : ((Subgroup.zpowers c).map s).comap (QuotientGroup.mk' C) ≤ Subgroup.zpowers g ⊔ C := by
      intro v hv
      obtain ⟨x, hx', e⟩ := hv
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
      have e2 : ((g ^ n : G) : G ⧸ C) = (v : G ⧸ C) := by
        have e' : (QuotientGroup.mk' C g) ^ n = QuotientGroup.mk' C v := by
          have e3 := e
          rw [map_zpow] at e3
          exact e3
        show QuotientGroup.mk' C (g ^ n) = QuotientGroup.mk' C v
        rw [map_zpow]
        exact e'
      have h3 : (g ^ n)⁻¹ * v ∈ C := QuotientGroup.eq.mp e2
      have := Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers g n) h3
      simpa using this
    refine hrel _ hR ?_ g ⟨c, Subgroup.mem_zpowers c, rfl⟩ hgx
    refine le_trans (Subgroup.commutator_mono hV hV) (le_trans (comm_sup (N := K) ?_ hCC ?_) hKy)
    · rw [commutator_zpowers_self]; exact bot_le
    · have hgI : Subgroup.zpowers g ≤ I := by
        rw [Subgroup.zpowers_le]; exact hPI hg
      exact le_trans (Subgroup.commutator_mono hgI le_rfl) hIC
  have hB : ⁅(⊤ : Subgroup G), P⁆ ≤ ky := by
    rw [Subgroup.commutator_le]
    intro u _ g hg
    exact hwild _ (Subgroup.commutator_le_right ⊤ P (Subgroup.commutator_mem_commutator trivial hg))
      (hx (Subgroup.commutator_mem_commutator trivial trivial))
  have hK : ⁅(⊤ : Subgroup G), K⁆ ≤ ky := (Subgroup.commutator_le_right _ _).trans hKy
  have hPKy : ⁅(⊤ : Subgroup G), P ⊔ K⁆ ≤ ky := comm_right_sup hB hK
  have hII : ⁅I, I⁆ ≤ ky := by
    refine le_trans (Subgroup.commutator_mono ht ht) (comm_sup ?_ ?_ ?_)
    · rw [commutator_zpowers_self]; exact bot_le
    · exact le_trans (Subgroup.commutator_mono le_top le_rfl) hPKy
    · exact le_trans (Subgroup.commutator_mono le_top le_rfl) hPKy
  have hIC' : ⁅I ⊔ C, I ⊔ C⁆ ≤ ky := comm_sup hII (hCC.trans hKy) (hIC.trans hKy)
  have hE : ⁅(⊤ : Subgroup G), I⁆ ≤ ky := by
    rw [Subgroup.commutator_le]
    intro u _ g hg
    exact hrel _ hSI hIC' _ (le_sup_left (a := I) (Subgroup.commutator_le_right ⊤ I
      (Subgroup.commutator_mem_commutator trivial hg)))
      (hx (Subgroup.commutator_mem_commutator trivial trivial))
  rw [← hsup]
  refine comm_sup hII ?_ ?_
  · rw [commutator_zpowers_self]; exact bot_le
  · rw [Subgroup.commutator_comm]
    exact le_trans (Subgroup.commutator_mono le_top le_rfl) hE

end Core3

end GlobalTheory.CompanionTheory.RelSym

namespace GlobalTheory.CompanionTheory.RelSym

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.WeilDeligne LocalGlobalAboveLAlt
open scoped commutatorElement

section Conc

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Unfold `Triv`. Rewrite using `[WD.charPol_mk, WD.lpDim_mk]`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Establish `h2 : IsNilpotent (a.ρ g - 1)` using `⟨Module.finrank ℂ (Fin n → ℂ), by`.

Use `LinearMap.aeval_self_charpoly (a.ρ g)` as an intermediate fact. Rewrite `this` using `[e]`. Simplify using `using this⟩`. Conclude with `sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple h2 (Module.End.IsSemisimple.sub_of_commute (Commute.one_right _) (a.semisimple _) Module.End.isSemisimple_id))`. Introduce `e`.

Rewrite using `[e]`. Conclude with `LinearMap.charpoly_one`.
-/
theorem triv_mk_iff {n : ℕ} (a : WDRep h (Fin n → ℂ)) (g : ↥(Weil h)) :
    Triv (WD.mk a) g ↔ a.ρ g = 1 := by
  unfold Triv
  rw [WD.charPol_mk, WD.lpDim_mk]
  constructor
  · intro e
    have h2 : IsNilpotent (a.ρ g - 1) := ⟨Module.finrank ℂ (Fin n → ℂ), by
      have := LinearMap.aeval_self_charpoly (a.ρ g)
      rw [e] at this
      simpa using this⟩
    exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple h2
      (Module.End.IsSemisimple.sub_of_commute (Commute.one_right _) (a.semisimple _)
        Module.End.isSemisimple_id))
  · intro e
    rw [e]
    exact LinearMap.charpoly_one

/- English proof (translation)
Consider the cases of `hU with`. Consider the case `top => simp`. Consider the case `step _ _ _ _ ho => exact ho`.
-/
theorem sub_isOpen {U : Subgroup ↥(Weil h)} (hU : LocalGlobalAboveLAlt.Sub U) :
    IsOpen {s : ↥(Ine (F := E) A) | ineIncl h s ∈ U} := by
  cases hU with
  | top => simp
  | step _ _ _ _ ho => exact ho

/- English proof (translation)
Establish `: IsGalois E Ω` using `IsAlgClosure.isGalois E Ω`. Take `⟨O, hO, rfl⟩` from `isOpen_induced_iff.mp hS`. Establish `hm : O ∈ nhds (1 : G E Ω)` using `hO.mem_nhds h1`. Take `⟨L, hfd, hn, hL⟩` from `(krullTopology_mem_nhds_one_iff_of_normal E Ω O).mp hm`. Establish `hg : IsGalois E L` using `{}`.

Conclude with `⟨L.fixingSubgroup, (InfiniteGalois.normal_iff_isGalois L).2 hg, IntermediateField.fixingSubgroup_isOpen L, fun s hs => hL hs⟩`.
-/
theorem exists_open_normal (S : Set ↥(Ine (F := E) A)) (hS : IsOpen S) (h1 : 1 ∈ S) :
    ∃ N : Subgroup (G E Ω), N.Normal ∧ IsOpen (N : Set (G E Ω)) ∧
      ∀ s : ↥(Ine (F := E) A), s.1 ∈ N → s ∈ S := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hS
  have hm : O ∈ nhds (1 : G E Ω) := hO.mem_nhds h1
  obtain ⟨L, hfd, hn, hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal E Ω O).mp hm
  have hg : IsGalois E L := {}
  exact ⟨L.fixingSubgroup, (InfiniteGalois.normal_iff_isGalois L).2 hg,
    IntermediateField.fixingSubgroup_isOpen L, fun s hs => hL hs⟩

/- English proof (translation)
Establish `hfin : Finite (𝓞 E ⧸ w.asIdeal)` using `w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot`. Establish `hnt : Nontrivial (𝓞 E ⧸ w.asIdeal)` using `Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top`. Establish `hd : IsDomain (𝓞 E ⧸ w.asIdeal)` using `Ideal.Quotient.isDomain _`. Take `⟨p, hp⟩` from `CharP.exists (𝓞 E ⧸ w.asIdeal)`. Establish `hp0 : p ≠ 0` using `CharP.char_ne_zero_of_finite (𝓞 E ⧸ w.asIdeal) p`.

Establish `hpp : p.Prime` using `(CharP.char_is_prime_or_zero (𝓞 E ⧸ w.asIdeal) p).resolve_right hp0`. Use `⟨p, hpp, ?_⟩` and prove the remaining obligations. Establish `hmem : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `CharP.cast_eq_zero _ p`.

Use `(hh ((p : ℕ) : 𝓞 E)).mpr hmem` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_prime_lt (hh : IsPlaceOver A w) :
    ∃ p : ℕ, p.Prime ∧ A.valuation ((p : ℕ) : Ω) < 1 := by
  have hfin : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  have hnt : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  have hd : IsDomain (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.isDomain _
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 E ⧸ w.asIdeal)
  have hp0 : p ≠ 0 := CharP.char_ne_zero_of_finite (𝓞 E ⧸ w.asIdeal) p
  have hpp : p.Prime := (CharP.char_is_prime_or_zero (𝓞 E ⧸ w.asIdeal) p).resolve_right hp0
  refine ⟨p, hpp, ?_⟩
  have hmem : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  have := (hh ((p : ℕ) : 𝓞 E)).mpr hmem
  simpa using this

/- English proof (translation)
Take `⟨⟨_, ψ, rfl⟩, hg⟩` from `IsCyclic.exists_generator (α := f.range)`. Use `⟨ψ, fun g => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `Subgroup.mem_zpowers_iff.mp (hg ⟨f g, g, rfl⟩)`. Conclude with `⟨n, (congrArg Subtype.val hn).symm⟩`.
-/
theorem exists_lift {G M : Type*} [Group G] [Group M] [IsCyclic M] (f : G →* M) :
    ∃ ψ : G, ∀ g : G, ∃ n : ℤ, f g = f ψ ^ n := by
  obtain ⟨⟨_, ψ, rfl⟩, hg⟩ := IsCyclic.exists_generator (α := f.range)
  refine ⟨ψ, fun g => ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨f g, g, rfl⟩)
  exact ⟨n, (congrArg Subtype.val hn).symm⟩

end Conc

end GlobalTheory.CompanionTheory.RelSym

namespace GlobalTheory.CompanionTheory.RelSym

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.WeilDeligne LocalGlobalAboveLAlt
open scoped commutatorElement

section Conc2

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

noncomputable def emb (U : Subgroup ↥(Weil h)) : ↥U →* G E Ω := (Weil h).subtype.comp U.subtype

/- English proof (translation)
Use `⟨fun n hn g => ?_⟩` and prove the remaining obligations. Rewrite `hn`, the goal using `[Subgroup.mem_subgroupOf]`. Conclude with `conj_mem_Wild (Ine_le_Dec A g.2) hn`.
-/
theorem wild_normal : ((Wild E A).subgroupOf (Ine (F := E) A)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact conj_mem_Wild (Ine_le_Dec A g.2) hn

/- English proof (translation)
Take `⟨γ, hγ⟩` from `GlobalTheory.TameInertiaGen.exists_tameGenAt E Ω w A hh`. Take `⟨hγ1, hγ2⟩` from `tameGenAt_iff.mp hγ`. Use `set J := (Wild E A).subgroupOf (Ine (F := E) A) ⊔ N.subgroupOf (Ine (F := E) A) with hJd`. Set `γ' : ↥(Ine (F` to `E) A) := ⟨γ, hγ1⟩`. Use `⟨QuotientGroup.mk γ', fun x => ?_⟩` and prove the remaining obligations.

Take `⟨σ, rfl⟩` from `QuotientGroup.mk_surjective x`. Establish `hcl` using `hγ2 σ.2`. Establish `ho : IsOpen ((fun x : G E Ω => σ.1⁻¹ * x) ⁻¹' (N : Set (G E Ω)))` using `hNo.preimage (continuous_const_mul _)`. Take `⟨a, ha1, ha2⟩` from `mem_closure_iff.mp hcl _ ho (by simp [N.one_mem])`. Set `B' : Subgroup (G E Ω)` to `((Subgroup.zpowers (QuotientGroup.mk' J γ')).comap (QuotientGroup.mk' J)).map (Ine (F := E) A).subtype`.

Establish `hle : Subgroup.closure (insert γ (Wild E A : Set (G E Ω))) ≤ B'`. Rewrite using `[Subgroup.closure_le]`. Introduce and unpack `u (rfl | hu)`. Conclude with `⟨γ', Subgroup.mem_zpowers _, rfl⟩`. Use `⟨⟨u, Wild_le_Ine hu⟩, ?_, rfl⟩` and prove the remaining obligations.

Establish `: QuotientGroup.mk' J (⟨u, Wild_le_Ine hu⟩ : ↥(Ine (F` using `E) A)) = 1 := by`. Use `(QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left ?_)` and prove the remaining obligations. Conclude with `hu`. Use `show QuotientGroup.mk' J (⟨u, Wild_le_Ine hu⟩ : ↥(Ine (F := E) A)) ∈ Subgroup.zpowers (QuotientGroup.mk' J γ')`. Rewrite using `[this]`.

Conclude with `one_mem _`. Take `⟨a', ha', rfl⟩` from `hle ha2`. Establish `e1 : (QuotientGroup.mk σ : ↥(Ine (F` using `E) A) ⧸ J) = QuotientGroup.mk a' := by`. Rewrite using `[QuotientGroup.eq]`. Use `Subgroup.mem_sup_right ?_` and prove the remaining obligations.

Conclude with `ha1`. Rewrite using `[e1]`. Conclude with `ha'`.
-/
theorem isCyclic_tame (hh : IsPlaceOver A w) (N : Subgroup (G E Ω)) [N.Normal]
    (hNo : IsOpen (N : Set (G E Ω))) [hJ : ((Wild E A).subgroupOf (Ine (F := E) A) ⊔
      N.subgroupOf (Ine (F := E) A)).Normal] :
    IsCyclic (↥(Ine (F := E) A) ⧸ ((Wild E A).subgroupOf (Ine (F := E) A) ⊔
      N.subgroupOf (Ine (F := E) A))) := by
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt E Ω w A hh
  obtain ⟨hγ1, hγ2⟩ := tameGenAt_iff.mp hγ
  set J := (Wild E A).subgroupOf (Ine (F := E) A) ⊔ N.subgroupOf (Ine (F := E) A) with hJd
  let γ' : ↥(Ine (F := E) A) := ⟨γ, hγ1⟩
  refine ⟨QuotientGroup.mk γ', fun x => ?_⟩
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  have hcl := hγ2 σ.2
  have ho : IsOpen ((fun x : G E Ω => σ.1⁻¹ * x) ⁻¹' (N : Set (G E Ω))) :=
    hNo.preimage (continuous_const_mul _)
  obtain ⟨a, ha1, ha2⟩ := mem_closure_iff.mp hcl _ ho (by simp [N.one_mem])
  let B' : Subgroup (G E Ω) :=
    ((Subgroup.zpowers (QuotientGroup.mk' J γ')).comap (QuotientGroup.mk' J)).map
      (Ine (F := E) A).subtype
  have hle : Subgroup.closure (insert γ (Wild E A : Set (G E Ω))) ≤ B' := by
    rw [Subgroup.closure_le]
    rintro u (rfl | hu)
    · exact ⟨γ', Subgroup.mem_zpowers _, rfl⟩
    · refine ⟨⟨u, Wild_le_Ine hu⟩, ?_, rfl⟩
      have : QuotientGroup.mk' J (⟨u, Wild_le_Ine hu⟩ : ↥(Ine (F := E) A)) = 1 := by
        refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left ?_)
        exact hu
      show QuotientGroup.mk' J (⟨u, Wild_le_Ine hu⟩ : ↥(Ine (F := E) A)) ∈ Subgroup.zpowers (QuotientGroup.mk' J γ')
      rw [this]
      exact one_mem _
  obtain ⟨a', ha', rfl⟩ := hle ha2
  have e1 : (QuotientGroup.mk σ : ↥(Ine (F := E) A) ⧸ J) = QuotientGroup.mk a' := by
    rw [QuotientGroup.eq]
    refine Subgroup.mem_sup_right ?_
    exact ha1
  rw [e1]
  exact ha'

/- English proof (translation)
Establish `hW` using `wild_normal (E := E) (A := A)`. Establish `hNi : (N.subgroupOf (Ine (F` using `E) A)).Normal := Subgroup.Normal.subgroupOf inferInstance _`. Use `set J := (Wild E A).subgroupOf (Ine (F := E) A) ⊔ N.subgroupOf (Ine (F := E) A) with hJd`. Establish `hJ : J.Normal` using `inferInstance`. Establish `hcyc` using `isCyclic_tame hh N hNo`.

Set `I : Subgroup ↥U` to `(Ine (F := E) A).comap (emb U)`. Set `g0 : ↥I →* ↥(Ine (F` to `E) A) := ((emb U).comp I.subtype).codRestrict _ (fun x => x.2)`. Take `⟨t0, ht0⟩` from `exists_lift ((QuotientGroup.mk' J).comp g0)`. Use `⟨t0.1, fun i hi => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `ht0 ⟨i, hi⟩`.

Set `i' : ↥I` to `⟨i, hi⟩ * t0 ^ (-n)`. Establish `h1 : QuotientGroup.mk' J (g0 i') = 1`. Establish `: ((QuotientGroup.mk' J).comp g0) i' = 1`. Simplify using `only [i', map_mul, map_zpow, hn]`. Simplify using the standard rewrite rules.

Conclude with `this`. Establish `h2 : g0 i' ∈ J` using `(QuotientGroup.eq_one_iff _).mp h1`. Establish `h3 : g0 i' ∈ ((J : Subgroup _) : Set _)` using `h2`. Rewrite `h3` using `[hJd, Subgroup.mul_normal]`. Take `⟨u, hu, v, hv, huv⟩` from `Set.mem_mul.mp h3`.

Set `b : ↥U` to `⟨ineIncl h v, hNU v hv⟩`. Use `⟨n, i'.1 * b⁻¹, b, ?_, hv, v.2, ?_⟩` and prove the remaining obligations. Establish `e : emb U (i'.1 * b⁻¹) = u.1`. Establish `e2 : (g0 i').1 = u.1 * v.1` using `by rw [← huv]; rfl`. Establish `e3 : emb U i'.1 = (g0 i').1` using `rfl`.

Rewrite using `[map_mul, map_inv, e3, e2]`. Establish `e4 : emb U b = v.1` using `rfl`. Rewrite using `[e4]`. Use `group`. Rewrite using `[e]`.

Conclude with `hu`. Establish `: (i'.1 : ↥U) = i * t0.1 ^ (-n)`. Simplify using `[i']`. Rewrite using `[inv_mul_cancel_right, this]`. Use `group`.
-/
theorem exists_tame (hh : IsPlaceOver A w) (U : Subgroup ↥(Weil h)) (N : Subgroup (G E Ω)) [N.Normal]
    (hNo : IsOpen (N : Set (G E Ω)))
    (hNU : ∀ s : ↥(Ine (F := E) A), s.1 ∈ N → ineIncl h s ∈ U) :
    ∃ t : ↥U, ∀ i : ↥U, emb U i ∈ Ine (F := E) A → ∃ (n : ℤ) (a b : ↥U),
      emb U a ∈ Wild E A ∧ emb U b ∈ N ∧ emb U b ∈ Ine (F := E) A ∧ i = a * b * t ^ n := by
  have hW := wild_normal (E := E) (A := A)
  have hNi : (N.subgroupOf (Ine (F := E) A)).Normal := Subgroup.Normal.subgroupOf inferInstance _
  set J := (Wild E A).subgroupOf (Ine (F := E) A) ⊔ N.subgroupOf (Ine (F := E) A) with hJd
  have hJ : J.Normal := inferInstance
  have hcyc := isCyclic_tame hh N hNo
  let I : Subgroup ↥U := (Ine (F := E) A).comap (emb U)
  let g0 : ↥I →* ↥(Ine (F := E) A) := ((emb U).comp I.subtype).codRestrict _ (fun x => x.2)
  obtain ⟨t0, ht0⟩ := exists_lift ((QuotientGroup.mk' J).comp g0)
  refine ⟨t0.1, fun i hi => ?_⟩
  obtain ⟨n, hn⟩ := ht0 ⟨i, hi⟩
  let i' : ↥I := ⟨i, hi⟩ * t0 ^ (-n)
  have h1 : QuotientGroup.mk' J (g0 i') = 1 := by
    have : ((QuotientGroup.mk' J).comp g0) i' = 1 := by
      simp only [i', map_mul, map_zpow, hn]
      simp
    exact this
  have h2 : g0 i' ∈ J := (QuotientGroup.eq_one_iff _).mp h1
  have h3 : g0 i' ∈ ((J : Subgroup _) : Set _) := h2
  rw [hJd, Subgroup.mul_normal] at h3
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.mp h3
  let b : ↥U := ⟨ineIncl h v, hNU v hv⟩
  refine ⟨n, i'.1 * b⁻¹, b, ?_, hv, v.2, ?_⟩
  · have e : emb U (i'.1 * b⁻¹) = u.1 := by
      have e2 : (g0 i').1 = u.1 * v.1 := by rw [← huv]; rfl
      have e3 : emb U i'.1 = (g0 i').1 := rfl
      rw [map_mul, map_inv, e3, e2]
      have e4 : emb U b = v.1 := rfl
      rw [e4]
      group
    rw [e]
    exact hu
  · have : (i'.1 : ↥U) = i * t0.1 ^ (-n) := by
      simp [i']
    rw [inv_mul_cancel_right, this]
    group

end Conc2

end GlobalTheory.CompanionTheory.RelSym

namespace GlobalTheory.CompanionTheory.RelSym

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.WeilDeligne LocalGlobalAboveLAlt
open scoped commutatorElement

section Conc3

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Establish `hgal : IsGalois E Ω` using `IsAlgClosure.isGalois E Ω`. Set `S : Set ↥(Ine (F` to `E) A) := {s | ineIncl h s ∈ U} ∩ ({s | f₁ (ineIncl h s) = 1} ∩ {s | f₂ (ineIncl h s) = 1})`. Establish `hS : IsOpen S` using `(sub_isOpen hU).inter (IsOpen.inter hf₁ hf₂)`. Establish `h1S : (1 : ↥(Ine (F` using `E) A)) ∈ S := by`. Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;> simp [U.one_mem]`.

Take `⟨N, hNn, hNo, hNS⟩` from `exists_open_normal S hS h1S`. Take `⟨t, ht⟩` from `exists_tame h U N hNo (fun s hs => (hNS s hs).1)`. Take `⟨ψ, hψ⟩` from `exists_lift ((degHom h).comp U.subtype)`. Take `⟨p, hp, hpv⟩` from `exists_prime_lt h`. Set `I : Subgroup ↥U` to `((degHom h).comp U.subtype).ker`.

Establish `memI : ∀ u : ↥U, u ∈ I ↔ emb U u ∈ Ine (F` using `E) A := by`. Introduce `u`. Rewrite using `[MonoidHom.mem_ker]`. Simplify using `only [MonoidHom.comp_apply, degHom_apply, Subgroup.subtype_apply]`. Rewrite using `[ofAdd_eq_one]`.

Conclude with `deg_eq_zero_iff`. Set `P : Subgroup ↥U` to `(Wild E A).comap (emb U)`. Establish `hPn : P.Normal`. Use `⟨fun n hn g => ?_⟩` and prove the remaining obligations. Use `show emb U (g * n * g⁻¹) ∈ Wild E A`.

Rewrite using `[map_mul, map_mul, map_inv]`. Conclude with `conj_mem_Wild (Weil_le_Dec h (g.1.2)) hn`. Set `K : Subgroup ↥U` to `N.comap (emb U) ⊓ I`. Establish `hKn : K.Normal`. Establish `: (N.comap (emb U)).Normal` using `Subgroup.Normal.comap inferInstance _`.

Use `infer_instance`. Set `kx : Subgroup ↥U` to `(f₁.comp U.subtype).ker`. Set `ky : Subgroup ↥U` to `(f₂.comp U.subtype).ker`. Establish `hPI : P ≤ I` using `fun a ha => (memI a).mpr (Wild_le_Ine ha)`. Establish `hNf : N.FiniteIndex`.

Use `Subgroup.quotient_finite_of_isOpen N hNo` as an intermediate fact. Conclude with `Subgroup.finiteIndex_of_finite_quotient`. Establish `hfin : K.relIndex I ≠ 0`. Rewrite using `[Subgroup.inf_relIndex_right]`. Establish `: (N.comap (emb U)).FiniteIndex` using `⟨by`.

Rewrite using `[Subgroup.index_comap]`. Conclude with `(inferInstance : (N.subgroupOf (emb U).range).FiniteIndex).index_ne_zero⟩`. Conclude with `(inferInstance : ((N.comap (emb U)).subgroupOf I).FiniteIndex).index_ne_zero`. Establish `hcomU : ⁅U, U⁆ = (⁅(⊤ : Subgroup ↥U), ⊤⁆ : Subgroup ↥U).map U.subtype`. Rewrite using `[Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]`.

Establish `hcore : ⁅(⊤ : Subgroup ↥U), ⊤⁆ ≤ ky`. Use `core hp K I P kx ky inf_le_right hPI hfin ψ t ?_ ?_ ?_ ?_ (fun V => LocalGlobalAboveLAlt.Sub (V.map U.subtype)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `g`. Take `⟨n, hn⟩` from `hψ g`. Use `⟨-n, ?_⟩` and prove the remaining obligations.

Rewrite using `[MonoidHom.mem_ker, map_mul, map_zpow, hn, zpow_neg, mul_inv_cancel]`. Introduce `i hi`. Take `⟨n, a, b, ha, hb1, hb2, e⟩` from `ht i ((memI i).mp hi)`. Rewrite using `[e]`. Use `mul_mem (mul_mem ?_ ?_) ?_` and prove the remaining obligations.

Conclude with `Subgroup.mem_sup_right (Subgroup.mem_sup_left ha)`. Conclude with `Subgroup.mem_sup_right (Subgroup.mem_sup_right ⟨hb1, (memI b).mpr hb2⟩)`. Conclude with `Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers t n)`. Introduce `g hg`. Take `⟨k, hk⟩` from `Formalism.MainNotions.N.KillingConditions.WildPf.wildProP E Ω A p hp hpv (emb U g) hg N hNo`.

Use `⟨k, ⟨?_, pow_mem (hPI hg) _⟩⟩` and prove the remaining obligations. Use `show emb U (g ^ p ^ k) ∈ N`. Rewrite using `[map_pow]`. Conclude with `hk`. Introduce `a ha`.

Establish `h2 : emb U a ∈ Ine (F` using `E) A := (memI a).mp ha.2`. Establish `h3` using `(hNS ⟨emb U a, h2⟩ ha.1).2.2`. Conclude with `h3`. Use `show LocalGlobalAboveLAlt.Sub ((⊤ : Subgroup ↥U).map U.subtype)`. Rewrite using `[← MonoidHom.range_eq_map, Subgroup.range_subtype]`.

Conclude with `hU`. Introduce `U' V hV hle hc hri hK`. Use `LocalGlobalAboveLAlt.Sub.step hV (Subgroup.map_mono hle) ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← Subgroup.map_commutator]`. Conclude with `Subgroup.map_mono hc`.

Rewrite using `[Subgroup.relIndex_map_map_of_injective _ _ U.subtype_injective]` and apply the resulting hypothesis. Establish `ho : IsOpen (((U'.map U.subtype).comap (ineIncl h) : Subgroup ↥(Ine (F` using `E) A)) : Set ↥(Ine (F := E) A)) := by`. Use `Subgroup.isOpen_mono (H₁ := N.comap (Ine (F := E) A).subtype) ?_ (hNo.preimage continuous_subtype_val)` and prove the remaining obligations. Introduce `s hs`. Use `⟨⟨ineIncl h s, (hNS s hs).1⟩, hK ⟨hs, (memI _).mpr s.2⟩, rfl⟩` and prove the remaining obligations.

Conclude with `ho`. Introduce `V hV hc g hg hgx`. Use `hrel (V.map U.subtype) hV (fun a ha => ?_) g.1 ⟨g, hg, rfl⟩ hgx` and prove the remaining obligations. Rewrite `ha` using `[← Subgroup.map_commutator]`. Take `⟨b, hb, rfl⟩` from `ha`.

Conclude with `hc hb`. Introduce `a ha`. Conclude with `hx a.1 (by rw [hcomU]; exact ⟨a, ha, rfl⟩)`. Introduce `g hg`. Rewrite `hg` using `[hcomU]`.

Take `⟨b, hb, rfl⟩` from `hg`. Conclude with `hcore hb`.
-/
theorem kills_commutators {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] (f₁ : ↥(Weil h) →* M₁)
    (f₂ : ↥(Weil h) →* M₂) (hf₁ : IsSmooth f₁) (hf₂ : IsSmooth f₂) (U : Subgroup ↥(Weil h))
    (hU : LocalGlobalAboveLAlt.Sub U)
    (hrel : ∀ V : Subgroup ↥(Weil h), LocalGlobalAboveLAlt.Sub V → (∀ g ∈ ⁅V, V⁆, f₂ g = 1) →
      ∀ g ∈ V, f₁ g = 1 → f₂ g = 1)
    (hx : ∀ g ∈ ⁅U, U⁆, f₁ g = 1) : ∀ g ∈ ⁅U, U⁆, f₂ g = 1 := by
  classical
  have hgal : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  let S : Set ↥(Ine (F := E) A) := {s | ineIncl h s ∈ U} ∩
    ({s | f₁ (ineIncl h s) = 1} ∩ {s | f₂ (ineIncl h s) = 1})
  have hS : IsOpen S := (sub_isOpen hU).inter (IsOpen.inter hf₁ hf₂)
  have h1S : (1 : ↥(Ine (F := E) A)) ∈ S := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [U.one_mem]
  obtain ⟨N, hNn, hNo, hNS⟩ := exists_open_normal S hS h1S
  obtain ⟨t, ht⟩ := exists_tame h U N hNo (fun s hs => (hNS s hs).1)
  obtain ⟨ψ, hψ⟩ := exists_lift ((degHom h).comp U.subtype)
  obtain ⟨p, hp, hpv⟩ := exists_prime_lt h
  let I : Subgroup ↥U := ((degHom h).comp U.subtype).ker
  have memI : ∀ u : ↥U, u ∈ I ↔ emb U u ∈ Ine (F := E) A := by
    intro u
    rw [MonoidHom.mem_ker]
    simp only [MonoidHom.comp_apply, degHom_apply, Subgroup.subtype_apply]
    rw [ofAdd_eq_one]
    exact deg_eq_zero_iff
  let P : Subgroup ↥U := (Wild E A).comap (emb U)
  have hPn : P.Normal := by
    refine ⟨fun n hn g => ?_⟩
    show emb U (g * n * g⁻¹) ∈ Wild E A
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_Wild (Weil_le_Dec h (g.1.2)) hn
  let K : Subgroup ↥U := N.comap (emb U) ⊓ I
  have hKn : K.Normal := by
    have : (N.comap (emb U)).Normal := Subgroup.Normal.comap inferInstance _
    infer_instance
  let kx : Subgroup ↥U := (f₁.comp U.subtype).ker
  let ky : Subgroup ↥U := (f₂.comp U.subtype).ker
  have hPI : P ≤ I := fun a ha => (memI a).mpr (Wild_le_Ine ha)
  have hNf : N.FiniteIndex := by
    have := Subgroup.quotient_finite_of_isOpen N hNo
    exact Subgroup.finiteIndex_of_finite_quotient
  have hfin : K.relIndex I ≠ 0 := by
    rw [Subgroup.inf_relIndex_right]
    have : (N.comap (emb U)).FiniteIndex := ⟨by
      rw [Subgroup.index_comap]
      exact (inferInstance : (N.subgroupOf (emb U).range).FiniteIndex).index_ne_zero⟩
    exact (inferInstance : ((N.comap (emb U)).subgroupOf I).FiniteIndex).index_ne_zero
  have hcomU : ⁅U, U⁆ = (⁅(⊤ : Subgroup ↥U), ⊤⁆ : Subgroup ↥U).map U.subtype := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcore : ⁅(⊤ : Subgroup ↥U), ⊤⁆ ≤ ky := by
    refine core hp K I P kx ky inf_le_right hPI hfin ψ t ?_ ?_ ?_ ?_
      (fun V => LocalGlobalAboveLAlt.Sub (V.map U.subtype)) ?_ ?_ ?_ ?_
    · intro g
      obtain ⟨n, hn⟩ := hψ g
      refine ⟨-n, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_zpow, hn, zpow_neg, mul_inv_cancel]
    · intro i hi
      obtain ⟨n, a, b, ha, hb1, hb2, e⟩ := ht i ((memI i).mp hi)
      rw [e]
      refine mul_mem (mul_mem ?_ ?_) ?_
      · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left ha)
      · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right ⟨hb1, (memI b).mpr hb2⟩)
      · exact Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers t n)
    · intro g hg
      obtain ⟨k, hk⟩ := Formalism.MainNotions.N.KillingConditions.WildPf.wildProP E Ω A p hp hpv (emb U g) hg N hNo
      refine ⟨k, ⟨?_, pow_mem (hPI hg) _⟩⟩
      show emb U (g ^ p ^ k) ∈ N
      rw [map_pow]
      exact hk
    · intro a ha
      have h2 : emb U a ∈ Ine (F := E) A := (memI a).mp ha.2
      have h3 := (hNS ⟨emb U a, h2⟩ ha.1).2.2
      exact h3
    · show LocalGlobalAboveLAlt.Sub ((⊤ : Subgroup ↥U).map U.subtype)
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hU
    · intro U' V hV hle hc hri hK
      refine LocalGlobalAboveLAlt.Sub.step hV (Subgroup.map_mono hle) ?_ ?_ ?_
      · rw [← Subgroup.map_commutator]
        exact Subgroup.map_mono hc
      · rwa [Subgroup.relIndex_map_map_of_injective _ _ U.subtype_injective]
      · have ho : IsOpen (((U'.map U.subtype).comap (ineIncl h) : Subgroup ↥(Ine (F := E) A)) :
            Set ↥(Ine (F := E) A)) := by
          refine Subgroup.isOpen_mono (H₁ := N.comap (Ine (F := E) A).subtype) ?_
            (hNo.preimage continuous_subtype_val)
          intro s hs
          refine ⟨⟨ineIncl h s, (hNS s hs).1⟩, hK ⟨hs, (memI _).mpr s.2⟩, rfl⟩
        exact ho
    · intro V hV hc g hg hgx
      refine hrel (V.map U.subtype) hV (fun a ha => ?_) g.1 ⟨g, hg, rfl⟩ hgx
      rw [← Subgroup.map_commutator] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      exact hc hb
    · intro a ha
      exact hx a.1 (by rw [hcomU]; exact ⟨a, ha, rfl⟩)
  intro g hg
  rw [hcomU] at hg
  obtain ⟨b, hb, rfl⟩ := hg
  exact hcore hb

end Conc3

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h x y hR`. Take `⟨hd, hm, hU⟩` from `hR`. Use `⟨hd.symm, hm.symm, fun U hS hT g hg => ?_⟩` and prove the remaining obligations. Take `⟨n, a, rfl⟩` from `WD.exists_rep x`. Take `⟨m, b, rfl⟩` from `WD.exists_rep y`.

Establish `hk` using `kills_commutators a.ρ b.ρ a.smooth b.smooth U hS (fun V hV hb g hg ha => by`. Use `(triv_mk_iff b g).mp ?_` and prove the remaining obligations. Establish `e` using `hU V hV (fun c hc => (triv_mk_iff b c).mpr (hb c hc)) g hg`. Establish `hta` using `(triv_mk_iff a g).mpr ha`. Unfold `Triv at hta ⊢`.

Rewrite using `[← e, ← hd]`. Conclude with `hta)`. Use the proof step `(fun c hc => (triv_mk_iff a c).mp (hT c hc))`. Conclude with `(hU U hS (fun c hc => (triv_mk_iff b c).mpr (hk c hc)) g hg).symm`.
-/
theorem relSymm : RelSymm := by
  intro E Ω _ _ _ _ _ A w h x y hR
  obtain ⟨hd, hm, hU⟩ := hR
  refine ⟨hd.symm, hm.symm, fun U hS hT g hg => ?_⟩
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  obtain ⟨m, b, rfl⟩ := WD.exists_rep y
  have hk := kills_commutators a.ρ b.ρ a.smooth b.smooth U hS (fun V hV hb g hg ha => by
      refine (triv_mk_iff b g).mp ?_
      have e := hU V hV (fun c hc => (triv_mk_iff b c).mpr (hb c hc)) g hg
      have hta := (triv_mk_iff a g).mpr ha
      unfold Triv at hta ⊢
      rw [← e, ← hd]
      exact hta)
    (fun c hc => (triv_mk_iff a c).mp (hT c hc))
  exact (hU U hS (fun c hc => (triv_mk_iff b c).mpr (hk c hc)) g hg).symm

end GlobalTheory.CompanionTheory.RelSym
