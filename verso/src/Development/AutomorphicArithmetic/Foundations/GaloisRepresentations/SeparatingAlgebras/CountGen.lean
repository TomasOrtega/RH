import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.sup_empty, Finset.card_empty, Nat.cast_zero, zero_mul]`. Conclude with `⟨inferInstance, by simp⟩`. Consider the case `insert i S hi ih`.

Take `⟨hfd, hle⟩` from `ih fun j hj => h j (Finset.mem_insert_of_mem hj)`. Take `⟨hfi, hli⟩` from `h i (Finset.mem_insert_self i S)`. Rewrite using `[Finset.sup_insert, Finset.card_insert_of_notMem hi]`. Use `⟨Submodule.finiteDimensional_sup _ _, ?_⟩` and prove the remaining obligations. Establish `h1 : (Module.finrank ℂ (A i ⊔ S.sup A : Submodule ℂ M) : ℝ) ≤ (Module.finrank ℂ (A i) : ℝ) + Module.finrank ℂ (S.sup A : Submodule ℂ M)`.

Conclude with `Submodule.finrank_add_le_finrank_add_finrank (A i) (S.sup A)` after adjusting the coercions. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem finset_sup_finrank_le {ι M : Type*} [AddCommGroup M] [Module ℂ M] (S : Finset ι)
    (A : ι → Submodule ℂ M) (r : ℝ)
    (h : ∀ i ∈ S, FiniteDimensional ℂ (A i) ∧ (Module.finrank ℂ (A i) : ℝ) ≤ r) :
    FiniteDimensional ℂ (S.sup A : Submodule ℂ M) ∧
      (Module.finrank ℂ (S.sup A : Submodule ℂ M) : ℝ) ≤ S.card * r := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact ⟨inferInstance, by simp⟩
  | insert i S hi ih =>
    obtain ⟨hfd, hle⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨hfi, hli⟩ := h i (Finset.mem_insert_self i S)
    rw [Finset.sup_insert, Finset.card_insert_of_notMem hi]
    refine ⟨Submodule.finiteDimensional_sup _ _, ?_⟩
    have h1 : (Module.finrank ℂ (A i ⊔ S.sup A : Submodule ℂ M) : ℝ) ≤
        (Module.finrank ℂ (A i) : ℝ) + Module.finrank ℂ (S.sup A : Submodule ℂ M) := by
      exact_mod_cast Submodule.finrank_add_le_finrank_add_finrank (A i) (S.sup A)
    push_cast
    linarith

/- English proof (translation)
Use `iSup₂_le fun π hπ => ?_` and prove the remaining obligations. Use `push_neg at hπ`. Take `⟨w, hw, hg⟩` from `hπ`. Use `le_trans ?_ (Finset.le_sup (f := fun w => part W C fun U => ¬ GenAt w (Φ w) U) hw)` and prove the remaining obligations. Conclude with `le_iSup₂_of_le (f := fun (π : AutSub E a) (_ : ¬ GenAt w (Φ w) π.V) => π.finPart W ⊓ fixedBy W C) π hg le_rfl`.
-/
private theorem part_le_sup {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (W : Wt E a)
    (C : Subgroup (UA E a)) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (Φ : HeightOneSpectrum (𝓞 E) → MvPolynomial (Fin a) ℂ) :
    part W C (fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) ≤
      S.sup fun w => part W C fun U => ¬ GenAt w (Φ w) U := by
  refine iSup₂_le fun π hπ => ?_
  push_neg at hπ
  obtain ⟨w, hw, hg⟩ := hπ
  refine le_trans ?_ (Finset.le_sup (f := fun w => part W C fun U => ¬ GenAt w (Φ w) U) hw)
  exact le_iSup₂_of_le (f := fun (π : AutSub E a) (_ : ¬ GenAt w (Φ w) π.V) => π.finPart W ⊓ fixedBy W C) π hg le_rfl

/- English proof (translation)
Introduce `hC hN E _ _ _ a w₀ hw₀ K hK J hJ W S Φ hD`. Take `⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (2 * ((S.card : ℝ) + 1))` from `⟨_, rfl⟩`. Establish `hc : (0 : ℝ) < (S.card : ℝ) + 1` using `by positivity`. Establish `hεpos : 0 < ε` using `by rw [hε]; positivity`. Establish `key : ∀ w, ∃ n₀ : ℕ, w ∈ S → ∀ n, n₀ ≤ n → FiniteDimensional ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) ∧ (Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) : ℝ) ≤ ε * Nat.card (J 0 ⧸ (J n).subgroupOf (J 0))`.

Introduce `w`. Distinguish the cases in `hw : w ∈ S`. Take `⟨n₀, h⟩` from `hC E a w₀ hw₀ K hK J hJ W _ (hN E a K w₀ w (hD.split w hw) (hD.apart w hw) (hD.hyp w hw) (Φ w) (hD.ne w hw)) ε hεpos`. Conclude with `⟨n₀, fun _ => h⟩`. Conclude with `⟨0, fun h => absurd h hw⟩`.

Use `choose n₀ hn₀ using key`. Use `⟨S.sup n₀, ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩ : ∃ n, n = S.sup n₀` from `⟨_, rfl⟩`. Rewrite using `[← hn]`. Establish `hall : ∀ w ∈ S, FiniteDimensional ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) ∧ (Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) : ℝ) ≤ ε * Nat.card (J 0 ⧸ (J n).subgroupOf (J 0))` using `fun w hw => hn₀ w hw n (hn ▸ Finset.le_sup (f := n₀) hw)`.

Take `⟨hfd, hle⟩` from `finset_sup_finrank_le S (fun w => part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) _ hall`. Establish `hsub` using `part_le_sup W (lev K w₀ (J n)) S Φ`. Use `⟨Submodule.finiteDimensional_of_le hsub, ?_⟩` and prove the remaining obligations. Establish `hmono` using `Submodule.finrank_mono hsub`. Establish `hmono' : (Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) : ℝ) ≤ Module.finrank ℂ (S.sup fun w => part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U : Submodule ℂ (algForms W))`.

Conclude with `hmono` after adjusting the coercions. Take `⟨N, hNdef⟩ : ∃ N : ℝ, N = Nat.card (J 0 ⧸ (J n).subgroupOf (J 0))` from `⟨_, rfl⟩`. Rewrite `hle` using `[← hNdef]`. Establish `hN0 : 0 ≤ N` using `by rw [hNdef]; positivity`. Establish `hfin : 2 * ((S.card : ℝ) * (ε * N)) ≤ N`.

Establish `h2 : 2 * ((S.card : ℝ) * (ε * N)) = (S.card : ℝ) / ((S.card : ℝ) + 1) * N`. Rewrite using `[hε]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h2]`. Establish `h3 : (S.card : ℝ) / ((S.card : ℝ) + 1) ≤ 1`.

Rewrite using `[div_le_one hc]`. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities. Establish `: (2 * Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) : ℝ) ≤ Nat.card (J 0 ⧸ (J n).subgroupOf (J 0))`. Rewrite using `[← hNdef]`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions.
-/
theorem UpperTheory.Gal.Gen.countGen_pf :
    UpperTheory.Gal.Gen.Count → UpperTheory.Gal.Gen.NeglAt → UpperTheory.Gal.Gen.CountGen := by
  classical
  intro hC hN E _ _ _ a w₀ hw₀ K hK J hJ W S Φ hD
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (2 * ((S.card : ℝ) + 1)) := ⟨_, rfl⟩
  have hc : (0 : ℝ) < (S.card : ℝ) + 1 := by positivity
  have hεpos : 0 < ε := by rw [hε]; positivity
  have key : ∀ w, ∃ n₀ : ℕ, w ∈ S → ∀ n, n₀ ≤ n →
      FiniteDimensional ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) ∧
      (Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) : ℝ) ≤
        ε * Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨n₀, h⟩ := hC E a w₀ hw₀ K hK J hJ W _
        (hN E a K w₀ w (hD.split w hw) (hD.apart w hw) (hD.hyp w hw) (Φ w) (hD.ne w hw)) ε hεpos
      exact ⟨n₀, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose n₀ hn₀ using key
  refine ⟨S.sup n₀, ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, n = S.sup n₀ := ⟨_, rfl⟩
  rw [← hn]
  have hall : ∀ w ∈ S, FiniteDimensional ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) ∧
      (Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) : ℝ) ≤
        ε * Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := fun w hw =>
    hn₀ w hw n (hn ▸ Finset.le_sup (f := n₀) hw)
  obtain ⟨hfd, hle⟩ := finset_sup_finrank_le S
    (fun w => part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) _ hall
  have hsub := part_le_sup W (lev K w₀ (J n)) S Φ
  refine ⟨Submodule.finiteDimensional_of_le hsub, ?_⟩
  have hmono := Submodule.finrank_mono hsub
  have hmono' : (Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) : ℝ) ≤
      Module.finrank ℂ (S.sup fun w => part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U :
        Submodule ℂ (algForms W)) := by
    exact_mod_cast hmono
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := ⟨_, rfl⟩
  rw [← hNdef] at hle
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  have hfin : 2 * ((S.card : ℝ) * (ε * N)) ≤ N := by
    have h2 : 2 * ((S.card : ℝ) * (ε * N)) = (S.card : ℝ) / ((S.card : ℝ) + 1) * N := by
      rw [hε]; field_simp
    rw [h2]
    have h3 : (S.card : ℝ) / ((S.card : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hc]; linarith
    nlinarith
  have : (2 * Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) : ℝ) ≤
      Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := by
    rw [← hNdef]; linarith
  exact_mod_cast this
