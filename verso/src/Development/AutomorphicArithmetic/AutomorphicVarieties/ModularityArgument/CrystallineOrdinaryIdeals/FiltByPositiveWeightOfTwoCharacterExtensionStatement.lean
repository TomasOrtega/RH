import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiltByRestrictScalarsOfResidualCharacters
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
/- English proof (translation)
Establish `step : ∀ W : Submodule E V, F' ≤ W → (∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = W ∧ ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i) → ∀ v ∈ F'', ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = W ⊔ E ∙ v …`. Introduce and unpack `W hW ⟨n, F, h0, hn, hs⟩ v hv`. Use `⟨n + 1, fun i => if i = n + 1 then W ⊔ E ∙ v else F i, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[h0]`. Simplify using the standard rewrite rules.

Introduce `i hi`. Distinguish the cases in `hin : i < n`. Establish `h1 : i ≠ n + 1` using `by omega`. Establish `h2 : i + 1 ≠ n + 1` using `by omega`. Simplify using `only [h1, h2, if_false]`.

Conclude with `hs i hin`. Establish `hi' : i = n` using `by omega`. Substitute `hi'` using the available equality. Establish `h1 : i ≠ i + 1` using `by omega`. Simplify using `only [h1, if_true, if_false, hn]`.

Conclude with `⟨le_sup_left, κ, hκ, v, rfl, fun g => hW (h v hv g)⟩`. Establish `key : ∀ s : Finset V, (↑s : Set V) ⊆ F'' → ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = F' ⊔ Submodule.span E (↑s : Set V) ∧ ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i`. Introduce `s`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`.

Simplify using `using hQ`. Introduce `a s _ ih hs`. Rewrite `hs`, the goal using `[Finset.coe_insert]`. Establish `h1` using `step (F' ⊔ Submodule.span E ↑s) le_sup_left (ih (fun z hz => hs (Set.mem_insert_of_mem a hz))) a (hs (Set.mem_insert a _))`. Rewrite using `[Submodule.span_insert, sup_comm (E ∙ a), ← sup_assoc]`.

Conclude with `h1`. Take `⟨s, hs⟩` from `(IsNoetherian.noetherian F'' : F''.FG)`. Take `⟨n, F, h0, hn, hst⟩` from `key s (by rw [← hs]; exact Submodule.subset_span)`. Use `⟨n, F, h0, ?_, hst⟩` and prove the remaining obligations. Rewrite using `[hn, hs, sup_eq_right.mpr hle]`.
-/
private theorem exists_character_filtration_of_sub_smul_mem {G E V : Type} [Group G] [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (ρ : Representation E G V) (S : Set (G →* Eˣ)) (F' F'' : Submodule E V)
    (hQ : ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = F' ∧ ∀ i < n, F i ≤ F (i + 1) ∧
      ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i)
    (hle : F' ≤ F'') (κ : G →* Eˣ) (hκ : κ ∈ S)
    (h : ∀ y ∈ F'', ∀ g : G, (ρ g) y - ((κ g : Eˣ) : E) • y ∈ F') :
    ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = F'' ∧ ∀ i < n, F i ≤ F (i + 1) ∧
      ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i := by
  classical
  have step : ∀ W : Submodule E V, F' ≤ W →
      (∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = W ∧ ∀ i < n, F i ≤ F (i + 1) ∧
        ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i) →
      ∀ v ∈ F'', ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = W ⊔ E ∙ v ∧
        ∀ i < n, F i ≤ F (i + 1) ∧
        ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i := by
    rintro W hW ⟨n, F, h0, hn, hs⟩ v hv
    refine ⟨n + 1, fun i => if i = n + 1 then W ⊔ E ∙ v else F i, ?_, ?_, ?_⟩
    · simp [h0]
    · simp
    · intro i hi
      by_cases hin : i < n
      · have h1 : i ≠ n + 1 := by omega
        have h2 : i + 1 ≠ n + 1 := by omega
        simp only [h1, h2, if_false]
        exact hs i hin
      · have hi' : i = n := by omega
        subst hi'
        have h1 : i ≠ i + 1 := by omega
        simp only [h1, if_true, if_false, hn]
        exact ⟨le_sup_left, κ, hκ, v, rfl, fun g => hW (h v hv g)⟩
  have key : ∀ s : Finset V, (↑s : Set V) ⊆ F'' →
      ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = F' ⊔ Submodule.span E (↑s : Set V) ∧
        ∀ i < n, F i ≤ F (i + 1) ∧
        ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      simpa using hQ
    · intro a s _ ih hs
      rw [Finset.coe_insert] at hs ⊢
      have h1 := step (F' ⊔ Submodule.span E ↑s) le_sup_left
        (ih (fun z hz => hs (Set.mem_insert_of_mem a hz))) a (hs (Set.mem_insert a _))
      rw [Submodule.span_insert, sup_comm (E ∙ a), ← sup_assoc]
      exact h1
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian F'' : F''.FG)
  obtain ⟨n, F, h0, hn, hst⟩ := key s (by rw [← hs]; exact Submodule.subset_span)
  refine ⟨n, F, h0, ?_, hst⟩
  rw [hn, hs, sup_eq_right.mpr hle]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ a b _ _ wa wb hwa hwb hIa hIb x hx`. Use `haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B`. Use `haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B`. Establish `hmemI : ∀ c : B, c - algebraMap E B (π c) ∈ RingHom.ker (π : B →+* E)`. Introduce `c`.

Rewrite using `[RingHom.mem_ker]`. Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `⟨M, hM⟩ : IsNilpotent (RingHom.ker (π : B →+* E)) := by`. Rewrite using `[Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]`. Introduce `c hc`.

Conclude with `mem_nilradical.mpr (hπ c (by simpa using hc))`. Use `set I := RingHom.ker (π : B →+* E) with hIdef`. Establish `hMz : ∀ c ∈ I ^ M, c = 0`. Introduce `c hc`. Rewrite `hc` using `[hM, Ideal.zero_eq_bot, Ideal.mem_bot]`.

Conclude with `hc`. Establish `hstep : ∀ (c : B) (k : ℕ) (y : B), y ∈ I ^ k → c * y - algebraMap E B (π c) * y ∈ I ^ (k + 1)`. Introduce `c k y hy`. Rewrite using `[← sub_mul, pow_succ']`. Conclude with `Ideal.mul_mem_mul (hmemI c) hy`.

Establish `hcyc : ∀ σ, Units.map (π : B →* E) (cycA l l B σ) = cycA l l E σ`. Introduce `σ`. Use `ext`. Simplify using `only [cycA, Units.coe_map, MonoidHom.comp_apply, MonoidHom.coe_coe]`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B, IsScalarTower.algebraMap_apply ℚ_[l] E B, AlgHom.commutes]`.

Conclude with `(IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E _).symm`. Establish `hwt : ∀ (c : G →* Bˣ) (w : ℤ), (∀ g, φ g ∈ Iq l → c g = cycA l l B (φ g) ^ w) → HasWeight φ ((Units.map (π : B →* E)).comp c) w`. Introduce `c w hc`. Use `⟨⊤, by simp, fun g _ hg => ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.comp_apply, hc g hg, map_zpow, hcyc]`.

Establish `hsm : ∀ (u : Bˣ) (y : B × B), ((Units.map (π : B →* E) u : Eˣ) : E) • y = (algebraMap E B (π u) * y.1, algebraMap E B (π u) * y.2)`. Introduce `u y`. Apply the tactic sequence `ext <;> simp [Algebra.smul_def]`. Unfold `FiltBy`. Use `set S : Set (G →* Eˣ) := {κ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} with hS`.

Establish `hSa : (Units.map (π : B →* E)).comp a ∈ S` using `⟨wa, hwa, hwt a wa hIa⟩`. Establish `hSb : (Units.map (π : B →* E)).comp b ∈ S` using `⟨wb, hwb, hwt b wb hIb⟩`. Use `set ρ := resCoef E (ext2 a b x hx) with hρdef`. Establish `hρ : ∀ g (y : B × B), ρ g y = ((a g : B) * y.1 + x g * (b g : B) * y.2, (b g : B) * y.2)` using `fun g y => rfl`. Use `set P1 : ℕ → Submodule E (B × B) := fun k => ((I ^ k).restrictScalars E).prod ⊥ with hP1`.

Use `set P2 : ℕ → Submodule E (B × B) := fun k => (⊤ : Submodule E B).prod ((I ^ k).restrictScalars E) with hP2`. Establish `mP1 : ∀ k z, z ∈ P1 k ↔ z.1 ∈ I ^ k ∧ z.2 = 0`. Introduce `k z`. Simplify using `[hP1, Submodule.mem_prod]`. Establish `mP2 : ∀ k z, z ∈ P2 k ↔ z.2 ∈ I ^ k`.

Introduce `k z`. Simplify using `[hP2, Submodule.mem_prod]`. Establish `Q0 : ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = ⊥ ∧ ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧ ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i` using `⟨0, fun _ => ⊥, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩`. Establish `hQ1 : ∀ j : ℕ, ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = P1 (M - j) ∧ ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧ ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero`. Use `exists_character_filtration_of_sub_smul_mem ρ S ⊥ (P1 (M - 0)) Q0 bot_le _ hSa ?_` and prove the remaining obligations. Introduce `y hy g`. Rewrite `hy` using `[mP1, Nat.sub_zero]`.

Establish `hy0 : y = 0` using `Prod.ext (hMz _ hy.1) hy.2`. Substitute `hy0` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ j ih`. Distinguish the cases in `hj : j < M`.

Establish `e : M - j = (M - (j + 1)) + 1` using `by omega`. Rewrite `ih` using `[e]`. Use `exists_character_filtration_of_sub_smul_mem ρ S _ _ ih ?_ _ hSa ?_` and prove the remaining obligations. Introduce `z hz`. Rewrite `hz`, the goal using `[mP1]`.

Conclude with `⟨Ideal.pow_le_pow_right (Nat.le_succ _) hz.1, hz.2⟩`. Introduce `y hy g`. Rewrite `hy` using `[mP1]`. Rewrite using `[mP1, MonoidHom.comp_apply, hsm, hρ]`. Use `⟨?_, by simp [hy.2]⟩` and prove the remaining obligations.

Simplify `hstep (a g : B) _ y.1 hy.1` using `[hy.2]`. Establish `e : M - (j + 1) = M - j` using `by omega`. Rewrite using `[e]`. Conclude with `ih`. Establish `T12 : ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = P2 M ∧ ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧ ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i`.

Establish `h1` using `hQ1 M`. Rewrite `h1` using `[Nat.sub_self]`. Use `exists_character_filtration_of_sub_smul_mem ρ S _ _ h1 ?_ _ hSa ?_` and prove the remaining obligations. Introduce `z hz`. Rewrite `hz` using `[mP1]`.

Rewrite using `[mP2, hz.2]`. Conclude with `zero_mem _`. Introduce `y hy g`. Rewrite `hy` using `[mP2]`. Establish `hy2` using `hMz _ hy`.

Rewrite using `[mP1, MonoidHom.comp_apply, hsm, hρ]`. Conclude with `⟨by simp, by simp [hy2]⟩`. Establish `hQ2 : ∀ j : ℕ, ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = P2 (M - j) ∧ ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧ ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero`. Rewrite using `[Nat.sub_zero]`. Conclude with `T12`. Consider the case `succ j ih`. Distinguish the cases in `hj : j < M`.

Establish `e : M - j = (M - (j + 1)) + 1` using `by omega`. Rewrite `ih` using `[e]`. Use `exists_character_filtration_of_sub_smul_mem ρ S _ _ ih ?_ _ hSb ?_` and prove the remaining obligations. Introduce `z hz`. Rewrite `hz`, the goal using `[mP2]`.

Conclude with `Ideal.pow_le_pow_right (Nat.le_succ _) hz`. Introduce `y hy g`. Rewrite `hy` using `[mP2]`. Rewrite using `[mP2, MonoidHom.comp_apply, hsm, hρ]`. Simplify using `using hstep (b g : B) _ y.2 hy`.

Establish `e : M - (j + 1) = M - j` using `by omega`. Rewrite using `[e]`. Conclude with `ih`. Take `⟨n, F, h0, hn, hs⟩` from `hQ2 M`. Establish `htop : P2 (M - M) = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `z _`. Rewrite using `[mP2, Nat.sub_self]`. Simplify using the standard rewrite rules. Conclude with `⟨n, F, h0, hn.trans htop, hs⟩`.
-/
theorem _root_.GlobalTheory.T.filtBy_positiveWeight_of_two_character_extension : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (a b : G →* Bˣ), Continuous (fun g => (a g : B)) → Continuous (fun g => (b g : B)) → ∀ wa wb : ℤ, 1 ≤ wa → 1 ≤ wb → (∀ g, φ g ∈ Iq l → a g = cycA l l B (φ g) ^ wa) → (∀ g, φ g ∈ Iq l → b g = cycA l l B (φ g) ^ wb) → ∀ (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((a / b) g : Bˣ) * x h), FiltBy (resCoef E (ext2 a b x hx)) {κ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ a b _ _ wa wb hwa hwb hIa hIb x hx
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  have hmemI : ∀ c : B, c - algebraMap E B (π c) ∈ RingHom.ker (π : B →+* E) := by
    intro c
    rw [RingHom.mem_ker]
    simp
  obtain ⟨M, hM⟩ : IsNilpotent (RingHom.ker (π : B →+* E)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro c hc
    exact mem_nilradical.mpr (hπ c (by simpa using hc))
  set I := RingHom.ker (π : B →+* E) with hIdef
  have hMz : ∀ c ∈ I ^ M, c = 0 := by
    intro c hc
    rw [hM, Ideal.zero_eq_bot, Ideal.mem_bot] at hc
    exact hc
  have hstep : ∀ (c : B) (k : ℕ) (y : B), y ∈ I ^ k →
      c * y - algebraMap E B (π c) * y ∈ I ^ (k + 1) := by
    intro c k y hy
    rw [← sub_mul, pow_succ']
    exact Ideal.mul_mem_mul (hmemI c) hy
  have hcyc : ∀ σ, Units.map (π : B →* E) (cycA l l B σ) = cycA l l E σ := by
    intro σ
    ext
    simp only [cycA, Units.coe_map, MonoidHom.comp_apply, MonoidHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B, IsScalarTower.algebraMap_apply ℚ_[l] E B,
      AlgHom.commutes]
    exact (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E _).symm
  have hwt : ∀ (c : G →* Bˣ) (w : ℤ), (∀ g, φ g ∈ Iq l → c g = cycA l l B (φ g) ^ w) →
      HasWeight φ ((Units.map (π : B →* E)).comp c) w := by
    intro c w hc
    refine ⟨⊤, by simp, fun g _ hg => ?_⟩
    rw [MonoidHom.comp_apply, hc g hg, map_zpow, hcyc]
  have hsm : ∀ (u : Bˣ) (y : B × B), ((Units.map (π : B →* E) u : Eˣ) : E) • y =
      (algebraMap E B (π u) * y.1, algebraMap E B (π u) * y.2) := by
    intro u y
    ext <;> simp [Algebra.smul_def]
  unfold FiltBy
  set S : Set (G →* Eˣ) := {κ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} with hS
  have hSa : (Units.map (π : B →* E)).comp a ∈ S := ⟨wa, hwa, hwt a wa hIa⟩
  have hSb : (Units.map (π : B →* E)).comp b ∈ S := ⟨wb, hwb, hwt b wb hIb⟩
  set ρ := resCoef E (ext2 a b x hx) with hρdef
  have hρ : ∀ g (y : B × B), ρ g y = ((a g : B) * y.1 + x g * (b g : B) * y.2, (b g : B) * y.2) :=
    fun g y => rfl
  set P1 : ℕ → Submodule E (B × B) := fun k => ((I ^ k).restrictScalars E).prod ⊥ with hP1
  set P2 : ℕ → Submodule E (B × B) := fun k => (⊤ : Submodule E B).prod ((I ^ k).restrictScalars E)
    with hP2
  have mP1 : ∀ k z, z ∈ P1 k ↔ z.1 ∈ I ^ k ∧ z.2 = 0 := by
    intro k z
    simp [hP1, Submodule.mem_prod]
  have mP2 : ∀ k z, z ∈ P2 k ↔ z.2 ∈ I ^ k := by
    intro k z
    simp [hP2, Submodule.mem_prod]
  have Q0 : ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = ⊥ ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i :=
    ⟨0, fun _ => ⊥, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  have hQ1 : ∀ j : ℕ, ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = P1 (M - j) ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i := by
    intro j
    induction j with
    | zero =>
      refine exists_character_filtration_of_sub_smul_mem ρ S ⊥ (P1 (M - 0)) Q0 bot_le _ hSa ?_
      intro y hy g
      rw [mP1, Nat.sub_zero] at hy
      have hy0 : y = 0 := Prod.ext (hMz _ hy.1) hy.2
      subst hy0
      simp
    | succ j ih =>
      by_cases hj : j < M
      · have e : M - j = (M - (j + 1)) + 1 := by omega
        rw [e] at ih
        refine exists_character_filtration_of_sub_smul_mem ρ S _ _ ih ?_ _ hSa ?_
        · intro z hz
          rw [mP1] at hz ⊢
          exact ⟨Ideal.pow_le_pow_right (Nat.le_succ _) hz.1, hz.2⟩
        · intro y hy g
          rw [mP1] at hy
          rw [mP1, MonoidHom.comp_apply, hsm, hρ]
          refine ⟨?_, by simp [hy.2]⟩
          simpa [hy.2] using hstep (a g : B) _ y.1 hy.1
      · have e : M - (j + 1) = M - j := by omega
        rw [e]
        exact ih
  have T12 : ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = P2 M ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i := by
    have h1 := hQ1 M
    rw [Nat.sub_self] at h1
    refine exists_character_filtration_of_sub_smul_mem ρ S _ _ h1 ?_ _ hSa ?_
    · intro z hz
      rw [mP1] at hz
      rw [mP2, hz.2]
      exact zero_mem _
    · intro y hy g
      rw [mP2] at hy
      have hy2 := hMz _ hy
      rw [mP1, MonoidHom.comp_apply, hsm, hρ]
      exact ⟨by simp, by simp [hy2]⟩
  have hQ2 : ∀ j : ℕ, ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = P2 (M - j) ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i := by
    intro j
    induction j with
    | zero =>
      rw [Nat.sub_zero]
      exact T12
    | succ j ih =>
      by_cases hj : j < M
      · have e : M - j = (M - (j + 1)) + 1 := by omega
        rw [e] at ih
        refine exists_character_filtration_of_sub_smul_mem ρ S _ _ ih ?_ _ hSb ?_
        · intro z hz
          rw [mP2] at hz ⊢
          exact Ideal.pow_le_pow_right (Nat.le_succ _) hz
        · intro y hy g
          rw [mP2] at hy
          rw [mP2, MonoidHom.comp_apply, hsm, hρ]
          simpa using hstep (b g : B) _ y.2 hy
      · have e : M - (j + 1) = M - j := by omega
        rw [e]
        exact ih
  obtain ⟨n, F, h0, hn, hs⟩ := hQ2 M
  have htop : P2 (M - M) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rw [mP2, Nat.sub_self]
    simp
  exact ⟨n, F, h0, hn.trans htop, hs⟩
